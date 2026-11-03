-- CONTROL ARM for the audit method.
-- Question: does `#print axioms` see through an `opaque` declaration whose
-- body is `sorry`? If it does not, an `opaque` would be an invisible axiom
-- and the axiom check in Scope.lean would be weaker than it looks.
--
-- Expected (audit method sound): both theorems report `sorryAx`.
-- Failure mode (audit method unsound): either reports an empty closure.

opaque hiddenFalse : False := by sorry

theorem controlViaOpaque : False := hiddenFalse

theorem controlDirect : False := by sorry

#print axioms controlViaOpaque
#print axioms controlDirect
