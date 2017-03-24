package kt17295

import java.lang.Thread.sleep
import kotlin.concurrent.timer

fun main(args: Array<String>) {
    timer("Repeating println", period=100) {
        //Breakpoint!
        println("Here")
        System.exit(0)
    }

    sleep(11111111)
}

// RESUME: 1