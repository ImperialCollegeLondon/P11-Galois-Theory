/- Group action on fields. -/

import group_theory.group_action data.equiv.ring

universes u v

variables (α : Type u) [group α] (β : Type v) [field β]

class group_field_action extends mul_action α β : Type ((max u v)+1) :=
(smul_add : ∀ (g : α) (x y : β), g • (x + y) = g • x + g • y)
(smul_one : ∀ (g : α), (g • 1 : β) = 1)
(smul_mul : ∀ (g : α) (x y : β), g • (x * y) = (g • x) * (g • y))

variables [group_field_action α β]

instance group_field_action.is_ring_hom (g : α) : is_ring_hom (mul_action.to_perm α β g) :=
{ map_one := group_field_action.smul_one g,
  map_mul := group_field_action.smul_mul g,
  map_add := group_field_action.smul_add g }

def group_field_action.ring_equiv (g : α) : β ≃+* β :=
ring_equiv.of (mul_action.to_perm α β g)
