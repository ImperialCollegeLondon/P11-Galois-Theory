import group_theory.group_action

universes u v

variables (α : Type u) [group α] {β : Type v} [mul_action α β] (x : β)

def of_quotient_stabilizer (g : quotient_group.quotient (mul_action.stabilizer α x)) : β :=
quotient.lift_on' g (•x) $ λ g1 g2 H,
calc  g1 • x
    = g1 • (g1⁻¹ * g2) • x : congr_arg _ H.symm
... = g2 • x : by rw [smul_smul, mul_inv_cancel_left]

theorem of_quotient_stabilizer_mk (g : α) : of_quotient_stabilizer α x (quotient_group.mk g) = g • x :=
rfl

theorem of_quotient_stabilizer_smul (g : α) (g' : quotient_group.quotient (mul_action.stabilizer α x)) :
  of_quotient_stabilizer α x (g • g') = g • of_quotient_stabilizer α x g' :=
quotient.induction_on' g' $ λ _, mul_smul _ _ _
