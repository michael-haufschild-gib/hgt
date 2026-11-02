import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFlowOnTheWindowAlgebra

/-!
# The twists of the tower

Pointwise multiplication by a **completely multiplicative** function `c` (`c(1) = 1`,
`c(mn) = c(m)c(n)`) is a ring endomorphism of the Dirichlet ring (`twistHom`): Dirichlet convolution
only multiplies the arguments. Two families of such twists act on the tower:

* the **Tate flow** `c = n^{−s}` (`tateTwist`), implemented on windows by conjugation with `e^{su}`;
* **character twists** `c = χ`, a real completely multiplicative character (Legendre symbols,
  `χ_{−4}`, …), which move the Euler datum of `ζ` to that of `L(s, χ)`.

They commute (`twist_tateTwist_comm`), and a twist carries the whole Tate structure of an Euler
datum to the twisted datum (`tateFamily_twist`): the Tate family of `(χζ, χμ)` is `χ·J_k`.

* **Twisted Tate pieces are character-weighted counts** (`tateFamily_charTwist_succ`): at
  `k = β + 1` they are `χ(m)φ(m)#ℙ^β(ℤ/m)`; the twisted windows of the degeneration read the same
  projective point counts, weighted by the character.
* **The non-Tate piece of a twisted datum is the twisted von Mangoldt weight**
  (`hasDerivAt_tateFamily_charTwist`): `∂_k(χJ_k)(m)|₀ = χ(m)Λ(m)`, the arithmetic weight of the
  window form of `L(s, χ)`.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory ArithmeticHodgeTheoryOfDegenerations

/-- A completely multiplicative real function on the positive integers. -/
structure IsCompletelyMultiplicative (c : ℕ → ℝ) : Prop where
  map_one : c 1 = 1
  map_mul : ∀ m n, c (m * n) = c m * c n

/-- The twist `f ↦ f·c`. -/
def twist (c : ℕ → ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * c n, by simp⟩

theorem twist_apply (c : ℕ → ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    twist c f n = f n * c n := rfl

theorem twist_mul {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c) (f g : ArithmeticFunction ℝ) :
    twist c (f * g) = twist c f * twist c g := by
  ext n
  rw [twist_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [twist_apply, twist_apply, ← (Nat.mem_divisorsAntidiagonal.mp hx).1, hc.map_mul]
  ring

theorem twist_one {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c) :
    twist c (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  rw [twist_apply, ArithmeticFunction.one_apply, ArithmeticFunction.one_apply]
  split_ifs with h
  · rw [h, hc.map_one, mul_one]
  · rw [zero_mul]

/-- **Completely multiplicative twists are ring endomorphisms of the Dirichlet ring.** -/
def twistHom {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c) :
    ArithmeticFunction ℝ →+* ArithmeticFunction ℝ where
  toFun := twist c
  map_one' := twist_one hc
  map_mul' := twist_mul hc
  map_zero' := by ext n; simp [twist_apply]
  map_add' f g := by ext n; simp [twist_apply, add_mul]

/-- The Tate flow is the twist by `n^{−s}`. -/
theorem tateTwist_eq_twist (s : ℝ) (f : ArithmeticFunction ℝ) :
    tateTwist s f = twist (fun n => (n : ℝ) ^ (-s)) f := rfl

/-- **Twists commute with the Tate flow.** -/
theorem twist_tateTwist_comm (c : ℕ → ℝ) (s : ℝ) (f : ArithmeticFunction ℝ) :
    twist c (tateTwist s f) = tateTwist s (twist c f) := by
  ext n; simp only [twist_apply, tateTwist_apply]; ring

/-- **A twist carries the Tate family**: the Tate family of `(F·c, G·c)` is `J^F_k·c`. -/
theorem tateFamily_twist {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c)
    (F G : ArithmeticFunction ℝ) (k : ℝ) :
    tateFamily (twist c F) (twist c G) k = twist c (tateFamily F G k) := by
  rw [tateFamily, tateFamily, twist_mul hc, twist_tateTwist_comm]

theorem twist_mul_inverse {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c)
    {F G : ArithmeticFunction ℝ} (hFG : F * G = 1) : twist c F * twist c G = 1 := by
  rw [← twist_mul hc, hFG, twist_one hc]

/-! ### Character twists of `ζ` -/

/-- The Euler datum of `L(s, χ)`: `(χζ, χμ)`. -/
def charZeta (c : ℕ → ℝ) : ArithmeticFunction ℝ :=
  twist c (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

def charMoebius (c : ℕ → ℝ) : ArithmeticFunction ℝ :=
  twist c (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

theorem charZeta_mul_charMoebius {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c) :
    charZeta c * charMoebius c = 1 :=
  twist_mul_inverse hc ArithmeticFunction.coe_zeta_mul_coe_moebius

/-- The Tate family of `L(s, χ)` is `χ·J_k`. -/
theorem tateFamily_charTwist {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c) (k : ℝ) (m : ℕ) :
    tateFamily (charZeta c) (charMoebius c) k m = c m * jordanTotient k m := by
  rw [charZeta, charMoebius, tateFamily_twist hc, tateFamily_zeta, twist_apply, jordanFun_apply,
    mul_comm]

/-- **Twisted Tate pieces are character-weighted projective point counts**:
`J^{χ}_{β+1}(m) = χ(m)φ(m)#ℙ^β(ℤ/m)`. -/
theorem tateFamily_charTwist_succ {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c) (β : ℕ)
    {m : ℕ} (hm : 1 ≤ m) :
    tateFamily (charZeta c) (charMoebius c) (β + 1 : ℕ) m =
      c m * ((Nat.card (ProjPoints (β + 1) m) : ℝ) * m.totient) := by
  rw [tateFamily_charTwist hc, jordanTotient_eq_card_projPoints β hm]

/-- **The non-Tate piece of `L(s, χ)` is the twisted von Mangoldt weight**:
`∂_k(χJ_k)(m)|_{k=0} = χ(m)Λ(m)`. -/
theorem hasDerivAt_tateFamily_charTwist {c : ℕ → ℝ} (hc : IsCompletelyMultiplicative c)
    (m : ℕ) :
    HasDerivAt (fun k => tateFamily (charZeta c) (charMoebius c) k m)
      (c m * ArithmeticFunction.vonMangoldt m) 0 := by
  simp_rw [tateFamily_charTwist hc]
  exact (hasDerivAt_jordanTotient_zero m).const_mul (c m)

end GaloisForLFunctions.WindowTowerOfSpecZ
