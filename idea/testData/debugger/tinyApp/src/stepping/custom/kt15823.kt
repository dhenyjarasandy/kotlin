package kt15823

object Some {
    val collection = mutableListOf<() -> Unit>()

    inline fun inlineWithReified(crossinline lambda: () -> Unit) {
        collection.add({ lambda() })
    }

    init {
        inlineWithReified {
            //Breakpoint!
            println("breakpoint here") //Will marked as (X), and never hit, but executes
        }
    }

    fun magic() {
        collection.forEach { it.invoke() }
    }
}

fun main(args: Array<String>) {
    Some.magic()
}

// RESUME: 1