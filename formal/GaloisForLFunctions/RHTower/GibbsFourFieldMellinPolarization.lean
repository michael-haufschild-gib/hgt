import GaloisForLFunctions.RHTower.FiniteExponentialSumMellin
import GaloisForLFunctions.RHTower.GibbsParityVortex

/-!
# The four parity-coarse Gibbs fields on the Mellin line

For disjoint finite prime sets `S` and `P` the four fields

```text
W = Σ_{T ⊆ P} Z_S(m_T x),   A = Σ_{T ⊆ P} J_S(m_T x),
B = Σ_{T ⊆ P} (-1)^{|T|} Z_S(m_T x),   J = Σ_{T ⊆ P} (-1)^{|T|} J_S(m_T x)
```

are finite exponential sums whose Mellin transforms are `Γ(s)` times the two finite Euler
characters.  The polarized line law then transports the literal antiscale determinant
`D = W A - B J` to an exact spectral integral.
-/

open Complex MeasureTheory Real Set Filter
open scoped FourierTransform Topology

noncomputable section

namespace RHTower

/-- The prime mass `m_U = ∏_{p ∈ U} p`. -/
def subsetMass (U : Finset ℕ) : ℝ := ∏ p ∈ U, (p : ℝ)

theorem subsetMass_nonneg (U : Finset ℕ) : 0 ≤ subsetMass U :=
  Finset.prod_nonneg fun p _ => by positivity

theorem one_le_subsetMass {U : Finset ℕ} (hU : ∀ p ∈ U, 0 < p) : 1 ≤ subsetMass U := by
  rw [subsetMass]
  have h : (∏ _p ∈ U, (1 : ℝ)) ≤ ∏ p ∈ U, (p : ℝ) := by
    refine Finset.prod_le_prod (fun p _ => by norm_num) (fun p hp => ?_)
    have := hU p hp
    exact_mod_cast this
  rwa [Finset.prod_const_one] at h

theorem subsetMass_pos {U : Finset ℕ} (hU : ∀ p ∈ U, 0 < p) : 0 < subsetMass U :=
  lt_of_lt_of_le zero_lt_one (one_le_subsetMass hU)

theorem subsetMass_cpow {U : Finset ℕ} (hU : ∀ p ∈ U, 0 < p) (s : ℂ) :
    ((subsetMass U : ℝ) : ℂ) ^ s = ∏ p ∈ U, ((p : ℝ) : ℂ) ^ s := by
  induction U using Finset.induction_on with
  | empty => simp [subsetMass]
  | @insert p U hp ih =>
      have hp0 : 0 < p := hU p (Finset.mem_insert_self p U)
      have hU' : ∀ q ∈ U, 0 < q := fun q hq => hU q (Finset.mem_insert_of_mem hq)
      have hmass : subsetMass (insert p U) = (p : ℝ) * subsetMass U := by
        rw [subsetMass, Finset.prod_insert hp, subsetMass]
      rw [hmass, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by positivity) (subsetMass_nonneg U) s, ih hU',
        Finset.prod_insert hp]

/-- The finite Euler character `∏_{p ∈ Q}(1 + ε p^{-s})`. -/
def eulerCharacter (Q : Finset ℕ) (e : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ Q, (1 + (e : ℂ) * ((p : ℝ) : ℂ) ^ (-s))

/-- Expanding the finite Euler character over subsets. -/
theorem sum_powerset_eq_eulerCharacter {Q : Finset ℕ} (hQ : ∀ p ∈ Q, 0 < p) (e : ℝ) (s : ℂ) :
    ∑ U ∈ Q.powerset, ((e : ℂ) ^ U.card * ((subsetMass U : ℝ) : ℂ) ^ (-s))
      = eulerCharacter Q e s := by
  rw [eulerCharacter]
  have h := Finset.prod_add (fun p : ℕ => (e : ℂ) * ((p : ℝ) : ℂ) ^ (-s))
    (fun _ : ℕ => (1 : ℂ)) Q
  have hone : ∀ T : Finset ℕ, (∏ _p ∈ Q \ T, (1 : ℂ)) = 1 := fun T => Finset.prod_const_one
  have hprod : ∀ T ∈ Q.powerset,
      (∏ p ∈ T, ((e : ℂ) * ((p : ℝ) : ℂ) ^ (-s))) * (∏ _p ∈ Q \ T, (1 : ℂ))
        = (e : ℂ) ^ T.card * ((subsetMass T : ℝ) : ℂ) ^ (-s) := by
    intro T hT
    have hTQ : T ⊆ Q := Finset.mem_powerset.mp hT
    have hT0 : ∀ p ∈ T, 0 < p := fun p hp => hQ p (hTQ hp)
    rw [hone T, mul_one, Finset.prod_mul_distrib, Finset.prod_const, subsetMass_cpow hT0]
  have hcomm : (∏ p ∈ Q, (1 + (e : ℂ) * ((p : ℝ) : ℂ) ^ (-s)))
      = ∏ p ∈ Q, ((e : ℂ) * ((p : ℝ) : ℂ) ^ (-s) + 1) :=
    Finset.prod_congr rfl fun p _ => by ring
  rw [hcomm, h]
  exact (Finset.sum_congr rfl hprod).symm

/-! ## The parity-coarse fields -/

/-- The parity-coarse field with sign `eS` on `S` and sign `eP` on `P`. -/
def gibbsCoarseField (S P : Finset ℕ) (eS eP : ℝ) (x : ℝ) : ℝ :=
  expDecaySum (S.powerset ×ˢ P.powerset)
    (fun q => eS ^ q.1.card * eP ^ q.2.card)
    (fun q => subsetMass q.1 * subsetMass q.2) x

/-- The complex-valued coarse field. -/
def gibbsCoarseFieldC (S P : Finset ℕ) (eS eP : ℝ) (x : ℝ) : ℂ :=
  ((gibbsCoarseField S P eS eP x : ℝ) : ℂ)

/-- The total coefficient mass of a coarse field. -/
def coarseFieldConst (S P : Finset ℕ) (eS eP : ℝ) : ℝ :=
  ∑ q ∈ S.powerset ×ˢ P.powerset, |eS ^ q.1.card * eP ^ q.2.card|

theorem continuous_gibbsCoarseFieldC (S P : Finset ℕ) (eS eP : ℝ) :
    Continuous (gibbsCoarseFieldC S P eS eP) := by
  unfold gibbsCoarseFieldC gibbsCoarseField
  exact Complex.continuous_ofReal.comp (continuous_expDecaySum _ _ _)

theorem norm_gibbsCoarseFieldC_le {S P : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (hP : ∀ p ∈ P, 0 < p)
    (eS eP : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖gibbsCoarseFieldC S P eS eP x‖ ≤ coarseFieldConst S P eS eP * Real.exp (-(1 * x)) := by
  have hrate : ∀ q ∈ S.powerset ×ˢ P.powerset, (1 : ℝ) ≤ subsetMass q.1 * subsetMass q.2 := by
    intro q hq
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hq
    have h1 : (1 : ℝ) ≤ subsetMass q.1 :=
      one_le_subsetMass fun p hp => hS p (hq.1 hp)
    have h2 : (1 : ℝ) ≤ subsetMass q.2 :=
      one_le_subsetMass fun p hp => hP p (hq.2 hp)
    nlinarith
  have h := abs_expDecaySum_le (S.powerset ×ˢ P.powerset)
    (fun q => eS ^ q.1.card * eP ^ q.2.card)
    (fun q => subsetMass q.1 * subsetMass q.2) hrate hx.le
  rw [gibbsCoarseFieldC, Complex.norm_real, Real.norm_eq_abs, coarseFieldConst]
  exact h

/-- **Mellin transform of a parity-coarse field**: `Γ(s)` times the two Euler characters. -/
theorem mellin_gibbsCoarseFieldC {S P : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (hP : ∀ p ∈ P, 0 < p)
    (eS eP : ℝ) {s : ℂ} (hs : 0 < s.re) :
    mellin (gibbsCoarseFieldC S P eS eP) s
      = Complex.Gamma s * (eulerCharacter S eS s * eulerCharacter P eP s) := by
  have hrate : ∀ q ∈ S.powerset ×ˢ P.powerset, (0 : ℝ) < subsetMass q.1 * subsetMass q.2 := by
    intro q hq
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hq
    exact mul_pos (subsetMass_pos fun p hp => hS p (hq.1 hp))
      (subsetMass_pos fun p hp => hP p (hq.2 hp))
  have hmellin := mellin_expDecaySum (S.powerset ×ˢ P.powerset)
    (fun q => eS ^ q.1.card * eP ^ q.2.card)
    (fun q => subsetMass q.1 * subsetMass q.2) hrate hs
  have hfun : gibbsCoarseFieldC S P eS eP
      = fun x : ℝ => ((expDecaySum (S.powerset ×ˢ P.powerset)
          (fun q => eS ^ q.1.card * eP ^ q.2.card)
          (fun q => subsetMass q.1 * subsetMass q.2) x : ℝ) : ℂ) := rfl
  rw [hfun, hmellin]
  congr 1
  have hsplit : ∀ q ∈ S.powerset ×ˢ P.powerset,
      ((eS ^ q.1.card * eP ^ q.2.card : ℝ) : ℂ) *
          ((subsetMass q.1 * subsetMass q.2 : ℝ) : ℂ) ^ (-s)
        = ((eS : ℂ) ^ q.1.card * ((subsetMass q.1 : ℝ) : ℂ) ^ (-s)) *
          ((eP : ℂ) ^ q.2.card * ((subsetMass q.2 : ℝ) : ℂ) ^ (-s)) := by
    intro q _
    have hmul : ((subsetMass q.1 * subsetMass q.2 : ℝ) : ℂ) ^ (-s)
        = ((subsetMass q.1 : ℝ) : ℂ) ^ (-s) * ((subsetMass q.2 : ℝ) : ℂ) ^ (-s) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (subsetMass_nonneg q.1)
        (subsetMass_nonneg q.2) (-s)]
    rw [hmul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_product,
    ← sum_powerset_eq_eulerCharacter hS eS s, ← sum_powerset_eq_eulerCharacter hP eP s,
    Finset.sum_mul_sum]

/-- The coarse field is the parity-weighted superposition of dilated Gibbs sections:
`Σ_{T ⊆ P} ε_P^{|T|} Z_S(m_T x)` for `ε_S = 1` and the signed section `J_S` for `ε_S = -1`. -/
theorem gibbsCoarseField_eq_sum_gibbsDiag (S P : Finset ℕ) (eS eP : ℝ) (x : ℝ) :
    gibbsCoarseField S P eS eP x
      = ∑ T ∈ P.powerset, eP ^ T.card * GibbsGas.gibbsDiag S (subsetMass T * x) eS := by
  rw [gibbsCoarseField, expDecaySum, Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [GibbsGas.gibbsDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [subsetMass]
  have hexp : Real.exp (-(subsetMass U * subsetMass T * x))
      = Real.exp (-(subsetMass T * x * ∏ p ∈ U, (p : ℝ))) := by
    congr 1
    rw [subsetMass, subsetMass]
    ring
  rw [subsetMass] at hexp
  rw [hexp]
  ring

/-! ## The literal antiscale determinant -/

/-- The literal parity determinant `D_{S,P} = W A - B J` of the four coarse fields. -/
def gibbsAntiscaleDeterminant (S P : Finset ℕ) (x : ℝ) : ℝ :=
  gibbsCoarseField S P 1 1 x * gibbsCoarseField S P (-1) 1 x
    - gibbsCoarseField S P 1 (-1) x * gibbsCoarseField S P (-1) (-1) x

theorem mellinConvergent_gibbsCoarseFieldC_mul {S P : Finset ℕ} (hS : ∀ p ∈ S, 0 < p)
    (hP : ∀ p ∈ P, 0 < p) (e1 e2 e3 e4 : ℝ) {sigma : ℝ} (hsigma : 0 < sigma) :
    MellinConvergent
      (fun x : ℝ => gibbsCoarseFieldC S P e1 e2 x * gibbsCoarseFieldC S P e3 e4 x)
      ((2 * sigma : ℝ) : ℂ) := by
  refine mellinConvergent_of_exp_bound (by linarith) (by norm_num : (0:ℝ) < 2)
    ((continuous_gibbsCoarseFieldC S P e1 e2).mul (continuous_gibbsCoarseFieldC S P e3 e4))
    (C := coarseFieldConst S P e1 e2 * coarseFieldConst S P e3 e4) (fun x hx => ?_)
  have h1 := norm_gibbsCoarseFieldC_le hS hP e1 e2 hx
  have h2 := norm_gibbsCoarseFieldC_le hS hP e3 e4 hx
  have h1n : (0 : ℝ) ≤ ‖gibbsCoarseFieldC S P e1 e2 x‖ := norm_nonneg _
  have h2n : (0 : ℝ) ≤ ‖gibbsCoarseFieldC S P e3 e4 x‖ := norm_nonneg _
  have hC1 : (0 : ℝ) ≤ coarseFieldConst S P e1 e2 := by
    have := Real.exp_pos (-(1 * x))
    nlinarith [h1, h1n]
  have hexp : Real.exp (-(1 * x)) * Real.exp (-(1 * x)) = Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_mul]
  calc ‖gibbsCoarseFieldC S P e1 e2 x‖ * ‖gibbsCoarseFieldC S P e3 e4 x‖
      ≤ (coarseFieldConst S P e1 e2 * Real.exp (-(1 * x))) *
          (coarseFieldConst S P e3 e4 * Real.exp (-(1 * x))) := by
        apply mul_le_mul h1 h2 h2n
        positivity
    _ = coarseFieldConst S P e1 e2 * coarseFieldConst S P e3 e4 * Real.exp (-(2 * x)) := by
        rw [← hexp]
        ring

/-- **The four-field Mellin--Plancherel polarization.**  The literal parity determinant of the
four coarse fields is the exact spectral integral of the Gamma mass against the source Euler pair
and the transverse Euler difference. -/
theorem integral_gammaNormSq_mul_eulerPair_eq_mellin_gibbsAntiscaleDeterminant
    {S P : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (hP : ∀ p ∈ P, 0 < p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ,
        (Complex.normSq (Complex.Gamma ((sigma : ℂ) + (t : ℂ) * I)) : ℂ) *
          (eulerCharacter S 1 ((sigma : ℂ) + (t : ℂ) * I) *
            (starRingEnd ℂ) (eulerCharacter S (-1) ((sigma : ℂ) + (t : ℂ) * I))) *
          ((Complex.normSq (eulerCharacter P 1 ((sigma : ℂ) + (t : ℂ) * I)) : ℂ) -
            (Complex.normSq (eulerCharacter P (-1) ((sigma : ℂ) + (t : ℂ) * I)) : ℂ)))
      = 2 * Real.pi *
        mellin (fun x : ℝ => ((gibbsAntiscaleDeterminant S P x : ℝ) : ℂ))
          ((2 * sigma : ℝ) : ℂ) := by
  have hL1 : ∀ e1 e2 : ℝ,
      Integrable (logMellinLineSource (gibbsCoarseFieldC S P e1 e2) sigma) := fun e1 e2 =>
    integrable_logMellinLineSource_of_exp_bound hsigma one_pos
      (continuous_gibbsCoarseFieldC S P e1 e2)
      (fun x hx => norm_gibbsCoarseFieldC_le hS hP e1 e2 hx)
  have hL2 : ∀ e1 e2 : ℝ,
      MemLp (logMellinLineSource (gibbsCoarseFieldC S P e1 e2) sigma) 2 volume := fun e1 e2 =>
    memLp_two_logMellinLineSource_of_exp_bound hsigma one_pos
      (continuous_gibbsCoarseFieldC S P e1 e2)
      (fun x hx => norm_gibbsCoarseFieldC_le hS hP e1 e2 hx)
  have hre : ∀ t : ℝ, ((sigma : ℂ) + (t : ℂ) * I).re = sigma := fun t => by simp
  have hline : ∀ (e1 e2 : ℝ) (t : ℝ),
      mellin (gibbsCoarseFieldC S P e1 e2) ((sigma : ℂ) + (t : ℂ) * I)
        = Complex.Gamma ((sigma : ℂ) + (t : ℂ) * I) *
          (eulerCharacter S e1 ((sigma : ℂ) + (t : ℂ) * I) *
            eulerCharacter P e2 ((sigma : ℂ) + (t : ℂ) * I)) := by
    intro e1 e2 t
    refine mellin_gibbsCoarseFieldC hS hP e1 e2 ?_
    rw [hre t]
    exact hsigma
  -- the two polarized pairings
  have hAW := integral_conj_mellin_line_mul_mellin_line
    (f := gibbsCoarseFieldC S P (-1) 1) (g := gibbsCoarseFieldC S P 1 1) (sigma := sigma)
    (hL1 (-1) 1) (hL2 (-1) 1) (hL1 1 1) (hL2 1 1)
  have hJB := integral_conj_mellin_line_mul_mellin_line
    (f := gibbsCoarseFieldC S P (-1) (-1)) (g := gibbsCoarseFieldC S P 1 (-1)) (sigma := sigma)
    (hL1 (-1) (-1)) (hL2 (-1) (-1)) (hL1 1 (-1)) (hL2 1 (-1))
  have hI1 := integrable_conj_mellin_line_mul_mellin_line
    (f := gibbsCoarseFieldC S P (-1) 1) (g := gibbsCoarseFieldC S P 1 1) (sigma := sigma)
    (hL1 (-1) 1) (hL2 (-1) 1) (hL1 1 1) (hL2 1 1)
  have hI2 := integrable_conj_mellin_line_mul_mellin_line
    (f := gibbsCoarseFieldC S P (-1) (-1)) (g := gibbsCoarseFieldC S P 1 (-1)) (sigma := sigma)
    (hL1 (-1) (-1)) (hL2 (-1) (-1)) (hL1 1 (-1)) (hL2 1 (-1))
  -- the pointwise spectral identity
  have hpoint : ∀ t : ℝ,
      (starRingEnd ℂ) (mellin (gibbsCoarseFieldC S P (-1) 1) ((sigma : ℂ) + (t : ℂ) * I)) *
          mellin (gibbsCoarseFieldC S P 1 1) ((sigma : ℂ) + (t : ℂ) * I)
        - (starRingEnd ℂ)
            (mellin (gibbsCoarseFieldC S P (-1) (-1)) ((sigma : ℂ) + (t : ℂ) * I)) *
          mellin (gibbsCoarseFieldC S P 1 (-1)) ((sigma : ℂ) + (t : ℂ) * I)
        = (Complex.normSq (Complex.Gamma ((sigma : ℂ) + (t : ℂ) * I)) : ℂ) *
          (eulerCharacter S 1 ((sigma : ℂ) + (t : ℂ) * I) *
            (starRingEnd ℂ) (eulerCharacter S (-1) ((sigma : ℂ) + (t : ℂ) * I))) *
          ((Complex.normSq (eulerCharacter P 1 ((sigma : ℂ) + (t : ℂ) * I)) : ℂ) -
            (Complex.normSq (eulerCharacter P (-1) ((sigma : ℂ) + (t : ℂ) * I)) : ℂ)) := by
    intro t
    rw [hline, hline, hline, hline, ← Complex.mul_conj, ← Complex.mul_conj, ← Complex.mul_conj]
    simp only [map_mul]
    ring
  -- the physical pairings are the two halves of the determinant
  have hreal : ∀ (e1 e2 e3 e4 : ℝ) (x : ℝ),
      (starRingEnd ℂ) (gibbsCoarseFieldC S P e1 e2 x) * gibbsCoarseFieldC S P e3 e4 x
        = ((gibbsCoarseField S P e1 e2 x * gibbsCoarseField S P e3 e4 x : ℝ) : ℂ) := by
    intro e1 e2 e3 e4 x
    rw [gibbsCoarseFieldC, gibbsCoarseFieldC, Complex.conj_ofReal, ← Complex.ofReal_mul]
  have hconv1 := mellinConvergent_gibbsCoarseFieldC_mul hS hP (-1) 1 1 1 hsigma
  have hconv2 := mellinConvergent_gibbsCoarseFieldC_mul hS hP (-1) (-1) 1 (-1) hsigma
  have hprod1 : (fun x : ℝ =>
      (starRingEnd ℂ) (gibbsCoarseFieldC S P (-1) 1 x) * gibbsCoarseFieldC S P 1 1 x)
      = fun x : ℝ => gibbsCoarseFieldC S P (-1) 1 x * gibbsCoarseFieldC S P 1 1 x := by
    funext x
    rw [gibbsCoarseFieldC, Complex.conj_ofReal]
  have hprod2 : (fun x : ℝ =>
      (starRingEnd ℂ) (gibbsCoarseFieldC S P (-1) (-1) x) * gibbsCoarseFieldC S P 1 (-1) x)
      = fun x : ℝ => gibbsCoarseFieldC S P (-1) (-1) x * gibbsCoarseFieldC S P 1 (-1) x := by
    funext x
    rw [gibbsCoarseFieldC, Complex.conj_ofReal]
  have hdet : mellin (fun x : ℝ =>
        (starRingEnd ℂ) (gibbsCoarseFieldC S P (-1) 1 x) * gibbsCoarseFieldC S P 1 1 x)
        ((2 * sigma : ℝ) : ℂ)
      - mellin (fun x : ℝ =>
        (starRingEnd ℂ) (gibbsCoarseFieldC S P (-1) (-1) x) * gibbsCoarseFieldC S P 1 (-1) x)
        ((2 * sigma : ℝ) : ℂ)
      = mellin (fun x : ℝ => ((gibbsAntiscaleDeterminant S P x : ℝ) : ℂ))
        ((2 * sigma : ℝ) : ℂ) := by
    rw [hprod1, hprod2]
    have hsub := (hasMellin_sub hconv1 hconv2).2
    rw [← hsub]
    refine congrArg (fun f : ℝ → ℂ => mellin f ((2 * sigma : ℝ) : ℂ)) ?_
    funext x
    rw [gibbsAntiscaleDeterminant, gibbsCoarseFieldC, gibbsCoarseFieldC, gibbsCoarseFieldC,
      gibbsCoarseFieldC]
    push_cast
    ring
  calc (∫ t : ℝ,
      (Complex.normSq (Complex.Gamma ((sigma : ℂ) + (t : ℂ) * I)) : ℂ) *
        (eulerCharacter S 1 ((sigma : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (eulerCharacter S (-1) ((sigma : ℂ) + (t : ℂ) * I))) *
        ((Complex.normSq (eulerCharacter P 1 ((sigma : ℂ) + (t : ℂ) * I)) : ℂ) -
          (Complex.normSq (eulerCharacter P (-1) ((sigma : ℂ) + (t : ℂ) * I)) : ℂ)))
      = ∫ t : ℝ,
          ((starRingEnd ℂ) (mellin (gibbsCoarseFieldC S P (-1) 1) ((sigma : ℂ) + (t : ℂ) * I)) *
            mellin (gibbsCoarseFieldC S P 1 1) ((sigma : ℂ) + (t : ℂ) * I)
          - (starRingEnd ℂ)
              (mellin (gibbsCoarseFieldC S P (-1) (-1)) ((sigma : ℂ) + (t : ℂ) * I)) *
            mellin (gibbsCoarseFieldC S P 1 (-1)) ((sigma : ℂ) + (t : ℂ) * I)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => (hpoint t).symm)
    _ = (∫ t : ℝ,
          (starRingEnd ℂ) (mellin (gibbsCoarseFieldC S P (-1) 1) ((sigma : ℂ) + (t : ℂ) * I)) *
            mellin (gibbsCoarseFieldC S P 1 1) ((sigma : ℂ) + (t : ℂ) * I))
        - ∫ t : ℝ,
          (starRingEnd ℂ)
              (mellin (gibbsCoarseFieldC S P (-1) (-1)) ((sigma : ℂ) + (t : ℂ) * I)) *
            mellin (gibbsCoarseFieldC S P 1 (-1)) ((sigma : ℂ) + (t : ℂ) * I) :=
        integral_sub hI1 hI2
    _ = 2 * Real.pi * mellin (fun x : ℝ =>
          (starRingEnd ℂ) (gibbsCoarseFieldC S P (-1) 1 x) * gibbsCoarseFieldC S P 1 1 x)
          ((2 * sigma : ℝ) : ℂ)
        - 2 * Real.pi * mellin (fun x : ℝ =>
          (starRingEnd ℂ) (gibbsCoarseFieldC S P (-1) (-1) x) * gibbsCoarseFieldC S P 1 (-1) x)
          ((2 * sigma : ℝ) : ℂ) := by rw [hAW, hJB]
    _ = 2 * Real.pi * mellin (fun x : ℝ => ((gibbsAntiscaleDeterminant S P x : ℝ) : ℂ))
          ((2 * sigma : ℝ) : ℂ) := by
        rw [← hdet]
        ring

end RHTower
