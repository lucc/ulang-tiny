package ulang

sealed trait Tactic
case class Ind(pat: Pat, kind: FixKind) extends Tactic
case class Split(pat: Pat) extends Tactic