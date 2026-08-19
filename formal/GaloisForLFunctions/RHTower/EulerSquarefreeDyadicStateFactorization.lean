import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicAffineProjection
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert

/-!
# Exact factorization of the pointed Euler state

`dyadic-squarefree-euler-fock-source-factorization`, §1–§2.

The arithmetic unitary of the card is the reindexing `n = m² d` followed by the Möbius parity
phase `μ(d)`:

```text
(U f)(d, m) = μ(d) · f (m² d).
```

This module builds it as an honest linear isometry equivalence of `ℓ²` spaces and proves the exact
pointed-state factorization

```text
U e_σ = s_σ ⊗ e_{2σ},
```

coordinate by coordinate, together with the mass identity `Z_sq(σ) · ζ(2σ) = ζ(σ)` that makes both
sides unit vectors.  Everything is source-side: no Xi, no divisor, no RH claim.
-/

open Complex Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## `ℓ²` membership from square summability -/

theorem memlp_two_of_summable_sq {ι : Type*} {f : ι → ℂ}
    (h : Summable (fun i => ‖f i‖ ^ (2 : ℕ))) : Memℓp f 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine h.congr fun i => ?_
  rw [← Real.rpow_natCast ‖f i‖ 2]
  norm_num

/-! ## Euler and squarefree masses -/

/-- `ζ(σ) = ∑_{n ≥ 1} n^{-σ}` as a real sum over the positive integers. -/
def eulerMass (σ : ℝ) : ℝ := ∑' n : ℕ+, (n : ℝ) ^ (-σ)

/-- `Z_sq(σ) = ∑_{d squarefree} d^{-σ}`. -/
def squarefreeMass (σ : ℝ) : ℝ := ∑' d : SquarefreePNat, ((d.1 : ℝ)) ^ (-σ)

theorem summable_pnat_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ+ => (n : ℝ) ^ (-σ)) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ σ)⁻¹) := Real.summable_nat_rpow_inv.mpr hσ
  have hnat' : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    refine hnat.congr fun n => ?_
    rw [Real.rpow_neg (by positivity)]
  exact hnat'.comp_injective (fun _ _ hab => PNat.coe_injective hab)

theorem summable_squarefree_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun d : SquarefreePNat => ((d.1 : ℝ)) ^ (-σ)) :=
  (summable_pnat_rpow hσ).comp_injective (fun _ _ hab => Subtype.ext hab)

theorem eulerMass_pos {σ : ℝ} (hσ : 1 < σ) : 0 < eulerMass σ := by
  have hs := summable_pnat_rpow hσ
  have hle : ((1 : ℕ+) : ℝ) ^ (-σ) ≤ eulerMass σ :=
    hs.le_tsum 1 (fun n _ => le_of_lt (by positivity))
  have h1 : (0 : ℝ) < ((1 : ℕ+) : ℝ) ^ (-σ) := by positivity
  linarith

theorem squarefreeMass_pos {σ : ℝ} (hσ : 1 < σ) : 0 < squarefreeMass σ := by
  have hs := summable_squarefree_rpow hσ
  set d₁ : SquarefreePNat := ⟨1, by simpa using squarefree_one⟩ with hd₁
  have hle : ((d₁.1 : ℝ)) ^ (-σ) ≤ squarefreeMass σ :=
    hs.le_tsum d₁ (fun d _ => le_of_lt (by positivity))
  have h1 : (0 : ℝ) < ((d₁.1 : ℝ)) ^ (-σ) := by positivity
  linarith

/-! ## The mass identity `(6)` -/

/-- The exact splitting of a single Euler weight along `n = m² d`, at every real exponent. -/
theorem rpow_dyadic_split (t : ℝ) (n : ℕ+) :
    (n : ℝ) ^ t
      = (((dyadicSquarefreeSquareEquiv n).1.1 : ℝ)) ^ t
        * (((dyadicSquarefreeSquareEquiv n).2 : ℝ)) ^ (2 * t) := by
  set d : ℕ+ := (dyadicSquarefreeSquareEquiv n).1.1 with hd
  set m : ℕ+ := (dyadicSquarefreeSquareEquiv n).2 with hm
  have hmul : ((m : ℕ) ^ 2 * (d : ℕ) : ℕ) = (n : ℕ) := dyadicSquarefreeSquareEquiv_mul n
  have hcast : (n : ℝ) = (m : ℝ) ^ 2 * (d : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hmul
    push_cast at h
    linarith [h]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := le_of_lt (by positivity)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := le_of_lt (by positivity)
  have hsplit : ((m : ℝ) ^ 2) ^ t = (m : ℝ) ^ (2 * t) := by
    rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul hm0]
    norm_num
  rw [hcast, Real.mul_rpow (by positivity) hd0, hsplit, mul_comm]

/-- The same splitting read backwards through the index equivalence. -/
theorem rpow_dyadic_split_symm (t : ℝ) (q : SquarefreePNat × ℕ+) :
    ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ) ^ t
      = ((q.1.1 : ℝ)) ^ t * ((q.2 : ℝ)) ^ (2 * t) := by
  have h := rpow_dyadic_split t (dyadicSquarefreeSquareEquiv.symm q)
  rwa [Equiv.apply_symm_apply] at h

/-- The exact splitting of a single Euler weight along `n = m² d`. -/
theorem rpow_eq_squarefree_mul_square {σ : ℝ} (n : ℕ+) :
    (n : ℝ) ^ (-σ)
      = (((dyadicSquarefreeSquareEquiv n).1.1 : ℝ)) ^ (-σ)
        * (((dyadicSquarefreeSquareEquiv n).2 : ℝ)) ^ (-(2 * σ)) := by
  have h := rpow_dyadic_split (-σ) n
  rw [show 2 * (-σ) = -(2 * σ) by ring] at h
  exact h

/-- **Equation (6).**  `Z_sq(σ) · ζ(2σ) = ζ(σ)`.  This is exactly the unique
squarefree-times-square decomposition, summed. -/
theorem squarefreeMass_mul_eulerMass_two_mul {σ : ℝ} (hσ : 1 < σ) :
    squarefreeMass σ * eulerMass (2 * σ) = eulerMass σ := by
  have hσ2 : 1 < 2 * σ := by linarith
  have hsq : Summable (fun d : SquarefreePNat => ‖((d.1 : ℝ)) ^ (-σ)‖) := by
    refine (summable_squarefree_rpow hσ).congr fun d => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hres : Summable (fun m : ℕ+ => ‖(m : ℝ) ^ (-(2 * σ))‖) := by
    refine (summable_pnat_rpow hσ2).congr fun m => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [squarefreeMass, eulerMass, tsum_mul_tsum_of_summable_norm hsq hres]
  rw [eulerMass, ← dyadicSquarefreeSquareEquiv.tsum_eq
    (fun q : SquarefreePNat × ℕ+ => ((q.1.1 : ℝ)) ^ (-σ) * ((q.2 : ℝ)) ^ (-(2 * σ)))]
  exact tsum_congr fun n => (rpow_eq_squarefree_mul_square n).symm

/-! ## The two pointed states -/

/-- The coordinates of the normalized Euler state. -/
def eulerStateCoord (σ : ℝ) (n : ℕ+) : ℂ :=
  (((n : ℝ) ^ (-σ / 2) / Real.sqrt (eulerMass σ) : ℝ) : ℂ)

/-- The coordinates of the signed squarefree parity state. -/
def squarefreeStateCoord (σ : ℝ) (d : SquarefreePNat) : ℂ :=
  (((ArithmeticFunction.moebius (d.1 : ℕ) : ℝ)
      * ((d.1 : ℝ) ^ (-σ / 2) / Real.sqrt (squarefreeMass σ)) : ℝ) : ℂ)

theorem abs_moebius_squarefree {n : ℕ} (hn : Squarefree n) :
    |(ArithmeticFunction.moebius n : ℝ)| = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn]
  rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num

theorem norm_eulerStateCoord {σ : ℝ} (hσ : 1 < σ) (n : ℕ+) :
    ‖eulerStateCoord σ n‖ ^ (2 : ℕ) = (n : ℝ) ^ (-σ) * (eulerMass σ)⁻¹ := by
  have hmass := eulerMass_pos hσ
  have hn : (0 : ℝ) < (n : ℝ) := by positivity
  have hsq : ((n : ℝ) ^ (-σ / 2)) ^ (2 : ℕ) = (n : ℝ) ^ (-σ) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ / 2)) 2, ← Real.rpow_mul (le_of_lt hn)]
    norm_num
  have hsr : Real.sqrt (eulerMass σ) ^ (2 : ℕ) = eulerMass σ := Real.sq_sqrt (le_of_lt hmass)
  rw [eulerStateCoord, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_pow, hsq, hsr, div_eq_mul_inv]

theorem norm_squarefreeStateCoord {σ : ℝ} (hσ : 1 < σ) (d : SquarefreePNat) :
    ‖squarefreeStateCoord σ d‖ ^ (2 : ℕ) = ((d.1 : ℝ)) ^ (-σ) * (squarefreeMass σ)⁻¹ := by
  have hmass := squarefreeMass_pos hσ
  have hn : (0 : ℝ) < ((d.1 : ℝ)) := by positivity
  have hmu := abs_moebius_squarefree d.2
  have hsq : (((d.1 : ℝ)) ^ (-σ / 2)) ^ (2 : ℕ) = ((d.1 : ℝ)) ^ (-σ) := by
    rw [← Real.rpow_natCast (((d.1 : ℝ)) ^ (-σ / 2)) 2, ← Real.rpow_mul (le_of_lt hn)]
    norm_num
  have hsr : Real.sqrt (squarefreeMass σ) ^ (2 : ℕ) = squarefreeMass σ :=
    Real.sq_sqrt (le_of_lt hmass)
  rw [squarefreeStateCoord, Complex.norm_real, Real.norm_eq_abs, abs_mul, hmu, one_mul,
    abs_of_nonneg (by positivity), div_pow, hsq, hsr, div_eq_mul_inv]

theorem memlp_eulerStateCoord {σ : ℝ} (hσ : 1 < σ) : Memℓp (eulerStateCoord σ) 2 := by
  refine memlp_two_of_summable_sq ?_
  exact ((summable_pnat_rpow hσ).mul_right (eulerMass σ)⁻¹).congr
    fun n => (norm_eulerStateCoord hσ n).symm

theorem memlp_squarefreeStateCoord {σ : ℝ} (hσ : 1 < σ) :
    Memℓp (squarefreeStateCoord σ) 2 := by
  refine memlp_two_of_summable_sq ?_
  exact ((summable_squarefree_rpow hσ).mul_right (squarefreeMass σ)⁻¹).congr
    fun d => (norm_squarefreeStateCoord hσ d).symm

/-- The normalized Euler state `e_σ(n) = n^{-σ/2}/√ζ(σ)`. -/
def eulerPointedState {σ : ℝ} (hσ : 1 < σ) : EulerPositiveL2 :=
  ⟨eulerStateCoord σ, memlp_eulerStateCoord hσ⟩

@[simp] theorem eulerPointedState_apply {σ : ℝ} (hσ : 1 < σ) (n : ℕ+) :
    eulerPointedState hσ n = eulerStateCoord σ n := rfl

/-- The signed squarefree parity state `s_σ(d) = μ(d) d^{-σ/2}/√Z_sq(σ)`. -/
def squarefreePointedState {σ : ℝ} (hσ : 1 < σ) : lp (fun _ : SquarefreePNat => ℂ) 2 :=
  ⟨squarefreeStateCoord σ, memlp_squarefreeStateCoord hσ⟩

@[simp] theorem squarefreePointedState_apply {σ : ℝ} (hσ : 1 < σ) (d : SquarefreePNat) :
    squarefreePointedState hσ d = squarefreeStateCoord σ d := rfl

/-! ### Both states are unit vectors -/

theorem norm_eulerPointedState {σ : ℝ} (hσ : 1 < σ) : ‖eulerPointedState hσ‖ = 1 := by
  have hmass := eulerMass_pos hσ
  have hsq : ‖eulerPointedState hσ‖ ^ 2 = 1 := by
    rw [lp_two_norm_sq_eq_tsum]
    have hterm : ∀ i : ℕ+, ‖(eulerPointedState hσ) i‖ ^ 2 = (i : ℝ) ^ (-σ) * (eulerMass σ)⁻¹ :=
      fun i => norm_eulerStateCoord hσ i
    rw [tsum_congr hterm, tsum_mul_right, ← eulerMass]
    field_simp
  rw [← Real.sqrt_sq (norm_nonneg (eulerPointedState hσ)), hsq, Real.sqrt_one]

theorem norm_squarefreePointedState {σ : ℝ} (hσ : 1 < σ) :
    ‖squarefreePointedState hσ‖ = 1 := by
  have hmass := squarefreeMass_pos hσ
  have hsq : ‖squarefreePointedState hσ‖ ^ 2 = 1 := by
    rw [lp_two_norm_sq_eq_tsum]
    have hterm : ∀ d : SquarefreePNat,
        ‖(squarefreePointedState hσ) d‖ ^ 2 = ((d.1 : ℝ)) ^ (-σ) * (squarefreeMass σ)⁻¹ :=
      fun d => norm_squarefreeStateCoord hσ d
    rw [tsum_congr hterm, tsum_mul_right, ← squarefreeMass]
    field_simp
  rw [← Real.sqrt_sq (norm_nonneg (squarefreePointedState hσ)), hsq, Real.sqrt_one]

/-! ## The signed arithmetic unitary `(4)` -/

/-- The Möbius parity phase of the squarefree coordinate. -/
def dyadicMoebiusPhase (q : SquarefreePNat × ℕ+) : ℂ :=
  ((ArithmeticFunction.moebius (q.1.1 : ℕ) : ℝ) : ℂ)

theorem norm_dyadicMoebiusPhase (q : SquarefreePNat × ℕ+) : ‖dyadicMoebiusPhase q‖ = 1 := by
  rw [dyadicMoebiusPhase, Complex.norm_real, Real.norm_eq_abs, abs_moebius_squarefree q.1.2]

/-- **The arithmetic unitary `(4)`.**  `(U f)(d, m) = μ(d) · f(m² d)`, a linear isometry
equivalence of the two source Hilbert spaces. -/
def dyadicSquarefreeSignedUnitary : EulerPositiveL2 ≃ₗᵢ[ℂ] DyadicSquarefreeL2 :=
  (lpReindexEquiv dyadicSquarefreeSquareEquiv).trans
    (lpPhaseUnitary dyadicMoebiusPhase norm_dyadicMoebiusPhase)

@[simp] theorem dyadicSquarefreeSignedUnitary_apply (x : EulerPositiveL2)
    (q : SquarefreePNat × ℕ+) :
    dyadicSquarefreeSignedUnitary x q
      = dyadicMoebiusPhase q * x (dyadicSquarefreeSquareEquiv.symm q) := rfl

/-! ## The exact pointed-state factorization `(7)`–`(8)` -/

/-- **Equation (7)/(8).**  The signed arithmetic unitary sends the pointed Euler state at `σ` to
the elementary tensor of the signed squarefree parity state at `σ` with the pointed Euler state at
`2σ`, coordinate by coordinate. -/
theorem dyadicSquarefreeSignedUnitary_eulerPointedState {σ : ℝ} (hσ : 1 < σ)
    (q : SquarefreePNat × ℕ+) :
    dyadicSquarefreeSignedUnitary (eulerPointedState hσ) q
      = squarefreeStateCoord σ q.1 * eulerStateCoord (2 * σ) q.2 := by
  have hσ2 : 1 < 2 * σ := by linarith
  have hZ := squarefreeMass_pos hσ
  have hE2 := eulerMass_pos hσ2
  have hmassEq := squarefreeMass_mul_eulerMass_two_mul hσ
  have hsplit := rpow_dyadic_split_symm (-σ / 2) q
  have hexp : 2 * (-σ / 2) = -(2 * σ) / 2 := by ring
  rw [hexp] at hsplit
  have hsqrt : Real.sqrt (eulerMass σ)
      = Real.sqrt (squarefreeMass σ) * Real.sqrt (eulerMass (2 * σ)) := by
    rw [← Real.sqrt_mul (le_of_lt hZ), hmassEq]
  rw [dyadicSquarefreeSignedUnitary_apply, eulerPointedState_apply, dyadicMoebiusPhase,
    eulerStateCoord, squarefreeStateCoord, eulerStateCoord]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [hsplit, hsqrt]
  field_simp

end RHTower
