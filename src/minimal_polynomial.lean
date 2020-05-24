import field_theory.minimal_polynomial
import .polynomial

universes u v

variables {α : Type u} {β : Type v}

namespace minimal_polynomial

open polynomial

theorem unique' [field α] [field β] [algebra α β] {x : β} (hx : is_integral α x)
  {p : polynomial α} (hp1 : _root_.irreducible p) (hp2 : polynomial.aeval α β x p = 0)
  (hp3 : p.monic) : p = minimal_polynomial hx :=
let ⟨q, hq⟩ := dvd hx hp2 in
polynomial.eq_of_monic_of_associated hp3 (monic hx) $
mul_one (minimal_polynomial hx) ▸ hq.symm ▸ associated_mul_mul (associated.refl _) $
associated_one_iff_is_unit.2 $ (hp1.is_unit_or_is_unit hq).resolve_left $ not_is_unit hx

end minimal_polynomial
