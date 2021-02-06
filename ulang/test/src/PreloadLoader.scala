import org.scalatest.{BeforeAndAfter, Suite}

trait PreloadLoader extends Suite with BeforeAndAfter {
  /** load the prelude file before each test */
  before { ulang.Main.loadPrelude() }
  /** reset the parsing and execution context after each test */
  after { ulang.context.clear }
}
