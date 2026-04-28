// should not import other sources that themselves import this file, to avoid circular dependencies
import { EventEmitter } from 'events'
import _ from 'lodash'
import assert from 'assert'

type ProcessExitHandler = (signal: string) => any
const cbsOnExit = new Set<{ cb: ProcessExitHandler, order: number }>()
export function onProcessExit(cb: ProcessExitHandler, order=10) {
    assert(Number.isInteger(order) && order >= 0, 'order must be an integer >= 0')
    const rec = { cb, order }
    cbsOnExit.add(rec)
    return () => cbsOnExit.delete(rec)
}

export let quitting = false
// 'exit' event is handled as the last resort, but it's not compatible with async callbacks
onFirstEvent(process, ['exit', 'SIGQUIT', 'SIGTERM', 'SIGINT', 'SIGHUP'], async signal => {
    console.log('Quitting with signal:', signal || 'unknown')
    quitting = true
    const byOrder = _.groupBy(Array.from(cbsOnExit), 'order') // this will be inherently ordered because keys are positive integers
    for (const recs of Object.values(byOrder))
        await Promise.allSettled(recs.map(({ cb }) => {
            try { return cb(signal) }
            // keep exit moving even when a synchronous cleanup fails after partially shutting down
            catch (e) {
                console.error("Error while quitting", e)
                return Promise.reject(e)
            }
        }))
    console.debug('Process exit')
    process.exit(0)
})

// keep calling cb in a sync fashion – returning a promise instead would break the code for argv.updating (update.ts)
export function onFirstEvent(emitter:EventEmitter, events: string[], cb: (...args:any[]) => void) {
    let already = false
    const cleanup = () => {
        events.forEach((e, i) => emitter.off(e, handlers[i]!))
    }
    const handlers = events.map(e => {
        const handler = (...args: any[]) => {
            if (already) return
            already = true
            cleanup()
            cb(e, ...args)
        }
        emitter.on(e, handler)
        return handler
    })
}
