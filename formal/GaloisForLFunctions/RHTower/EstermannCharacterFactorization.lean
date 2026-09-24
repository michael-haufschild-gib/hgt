import GaloisForLFunctions.RHTower.EstermannZeta
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# The character components of the Estermann regular part factor as L-function products

The twist enters `estermannRegularPart q a s = ∑_{c ≠ 0} E(ac/q, s)(ζ(s, c/q) − ζ(s))` only through
the dilation `c ↦ ac`. For a prime modulus every nonzero residue is a unit, so averaging against a
non-principal character `χ⁻¹` turns that dilation into a character value and the two factors
separate:

`∑_a χ⁻¹(a) R_a(s) = L(𝓕(χ⁻¹ ∘ neg), s) · q^s · L(χ, s)`.

Both factors are L-functions of functions on `ZMod q`; for primitive `χ` the discrete Fourier
transform of `χ⁻¹` is a Gauss sum times `χ`, so the right side is a Gauss-sum multiple of
`q^s L(s,χ)²`. So the family's deformation away from its `a`-independent part `q^{1−2s}ζ(s)²` is,
component by component, a **square of a Dirichlet L-function** weighted by a Gauss sum: `ζ²` is the
principal component of a representation of `(ZMod q)ˣ` whose isotypic pieces are the `L(s,χ)²`.
-/

open Complex HurwitzZeta

namespace RHTower

noncomputable section

/-- The `χ`-twisted exponential zeta of the modulus, as the L-function of a discrete Fourier
transform. -/
theorem sum_char_expZeta (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (s : ℂ) (h0 : Φ 0 = 0) :
    ∑ j : ZMod q, Φ j * expZeta (ZMod.toAddCircle j) s
      = ZMod.LFunction (ZMod.dft (fun j => Φ (-j))) s := by
  have hdft := ZMod.LFunction_dft (fun j : ZMod q => Φ (-j)) (N := q)
    (s := s) (Or.inl (by simpa using h0))
  rw [hdft]
  refine (Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun j => ?_)).symm
  simp only [Equiv.neg_apply]

/-- The Hurwitz decomposition of the L-function, in the form used below. -/
theorem sum_char_hurwitzZeta (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (s : ℂ) :
    ∑ c : ZMod q, Φ c * hurwitzZeta (ZMod.toAddCircle c) s
      = (q : ℂ) ^ s * ZMod.LFunction Φ s := by
  have hq : ((q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [ZMod.LFunction, ← mul_assoc, ← Complex.cpow_add _ _ hq]
  simp

/-- **The character components factor.**  For a prime modulus and a non-principal character, the
`χ⁻¹`-average of the Estermann regular part is a product of two L-functions. -/
theorem sum_char_estermannRegularPart (q : ℕ) [hq : Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : χ ≠ 1) (s : ℂ) :
    ∑ a : ZMod q, (χ⁻¹ a) * estermannRegularPart q a s
      = ZMod.LFunction (ZMod.dft (fun j => χ⁻¹ (-j))) s * ((q : ℂ) ^ s * ZMod.LFunction (⇑χ) s) := by
  classical
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hchi0 : χ⁻¹ (0 : ZMod q) = 0 := by
    refine MulChar.map_nonunit _ ?_
    simp
  set G : ℂ := ZMod.LFunction (ZMod.dft (fun j => χ⁻¹ (-j))) s with hG
  have hswap : ∑ a : ZMod q, (χ⁻¹ a) * estermannRegularPart q a s
      = ∑ c ∈ Finset.univ.erase (0 : ZMod q),
          (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s) *
            ∑ a : ZMod q, (χ⁻¹ a) * expZeta (ZMod.toAddCircle (a * c)) s := by
    simp only [estermannRegularPart, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hinner : ∀ c ∈ Finset.univ.erase (0 : ZMod q),
      (∑ a : ZMod q, (χ⁻¹ a) * expZeta (ZMod.toAddCircle (a * c)) s) = χ c * G := by
    intro c hc
    have hc0 : c ≠ 0 := Finset.ne_of_mem_erase hc
    have hreindex : (∑ a : ZMod q, (χ⁻¹ a) * expZeta (ZMod.toAddCircle (a * c)) s)
        = ∑ j : ZMod q, (χ⁻¹ (j * c⁻¹)) * expZeta (ZMod.toAddCircle j) s := by
      refine Fintype.sum_equiv (Equiv.mulRight₀ c hc0) _ _ (fun a => ?_)
      simp only [Equiv.mulRight₀_apply]
      rw [mul_inv_cancel_right₀ hc0]
    rw [hreindex]
    have hval : ∀ j : ZMod q, (χ⁻¹ (j * c⁻¹)) = χ c * χ⁻¹ j := by
      intro j
      rw [map_mul]
      have : χ⁻¹ (c⁻¹) = χ c := by
        rw [MulChar.inv_apply', inv_inv]
      rw [this]
      ring
    simp only [hval, mul_assoc]
    rw [← Finset.mul_sum, hG, ← sum_char_expZeta q (fun j => χ⁻¹ j) s hchi0]
  have hstep : ∑ c ∈ Finset.univ.erase (0 : ZMod q),
      (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s) *
        (∑ a : ZMod q, (χ⁻¹ a) * expZeta (ZMod.toAddCircle (a * c)) s)
      = ∑ c ∈ Finset.univ.erase (0 : ZMod q),
        (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s) * (χ c * G) :=
    Finset.sum_congr rfl (fun c hc => by rw [hinner c hc])
  have houter : ∑ c ∈ Finset.univ.erase (0 : ZMod q),
      (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s) * (χ c * G)
      = G * ((q : ℂ) ^ s * ZMod.LFunction (⇑χ) s) := by
    have hchizero : χ (0 : ZMod q) = 0 := by
      refine MulChar.map_nonunit _ ?_
      simp
    have hfull : ∑ c ∈ Finset.univ.erase (0 : ZMod q),
        (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s) * (χ c * G)
        = ∑ c : ZMod q, (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s) * (χ c * G) := by
      refine Finset.sum_erase Finset.univ ?_
      rw [hchizero]
      ring
    rw [hfull]
    have hsplit : ∑ c : ZMod q, (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s) * (χ c * G)
        = G * (∑ c : ZMod q, χ c * hurwitzZeta (ZMod.toAddCircle c) s)
          - G * riemannZeta s * ∑ c : ZMod q, χ c := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun c _ => by ring)
    rw [hsplit, MulChar.sum_eq_zero_of_ne_one hχ, sum_char_hurwitzZeta q (⇑χ) s]
    ring
  rw [hswap, hstep, houter]

end

end RHTower
