import GaloisForLFunctions.HTGeometry.GammaSimpleZeroBellHorizon
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator
import GaloisForLFunctions.HTGeometry.MeromorphicNormalizedRemovable

/-!
# The analytic reciprocal-Gamma Bell horizon

This module upgrades the algebraic principal-profile law to the actual meromorphic germs of the
normalized reciprocal-Gamma zero branches.  If `G` is the local simple-zero section, the
Bell-covariant coordinates are `G⁽ᵏ⁺¹⁾ / G`.  Multiplying each coordinate by the local parameter
has a finite boundary limit.  For an arbitrary polynomial observable `P`, multiplication by
`z ^ P.totalDegree` therefore converges to the evaluation of the top homogeneous component on the
boundary residue frame.

The reciprocal-Gamma residue frames are algebraically free in the eventual branch-germ ring.
Consequently every nonzero top sector is detected on branches arbitrarily far along the negative
Gamma poles, where its exact meromorphic order is minus its total degree.  It follows that the
observables with at most simple poles on the entire tower are exactly the affine polynomials in
the Bell-covariant coordinates.

Finally, the generic analytic Bell identity conjugates raw logarithmic-derivative jets to the
covariant coordinates on punctured neighborhoods.  This yields the complete raw classification:
an observable in `g, g', ..., g⁽ⁿ⁾` has at most simple poles throughout the tower exactly when it
is the complete-Bell image of an affine covariant polynomial.
-/

open Filter Topology MvPolynomial Polynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaAnalyticHorizonNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

theorem tendsto_mvPolynomial_eval
    {ι : Type*} [Fintype ι]
    {l : Filter ℂ} {x : ι → ℂ → ℂ} {r : ι → ℂ}
    (hx : ∀ i, Tendsto (x i) l (𝓝 (r i)))
    (P : MvPolynomial ι ℂ) :
    Tendsto (fun z => MvPolynomial.eval (fun i => x i z) P) l
      (𝓝 (MvPolynomial.eval r P)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using tendsto_const_nhds
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP => simpa using hP.mul (hx i)

theorem pow_totalDegree_mul_eval_eq_sum_homogeneousComponent
    {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℂ) (x : ι → ℂ) (z : ℂ) :
    z ^ P.totalDegree * MvPolynomial.eval x P =
      ∑ d ∈ Finset.range (P.totalDegree + 1),
        z ^ (P.totalDegree - d) *
          MvPolynomial.eval (fun i => z * x i)
            (MvPolynomial.homogeneousComponent d P) := by
  classical
  let D := P.totalDegree
  have hsum :
      (∑ d ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent d P) = P := by
    simpa [D] using MvPolynomial.sum_homogeneousComponent P
  calc
    z ^ P.totalDegree * MvPolynomial.eval x P =
        z ^ D * MvPolynomial.eval x
          (∑ d ∈ Finset.range (D + 1),
            MvPolynomial.homogeneousComponent d P) := by rw [hsum]
    _ = z ^ D * ∑ d ∈ Finset.range (D + 1),
          MvPolynomial.eval x (MvPolynomial.homogeneousComponent d P) := by rw [map_sum]
    _ = ∑ d ∈ Finset.range (D + 1),
          z ^ D * MvPolynomial.eval x (MvPolynomial.homogeneousComponent d P) := by
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdD : d ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
      have hscale := GaloisForLFunctions.isHomogeneous_eval₂_scale
        (MvPolynomial.homogeneousComponent_isHomogeneous d P)
        (RingHom.id ℂ) x z
      change MvPolynomial.eval (fun i => z * x i)
          (MvPolynomial.homogeneousComponent d P) =
        z ^ d * MvPolynomial.eval x (MvPolynomial.homogeneousComponent d P) at hscale
      rw [hscale, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hdD]

theorem tendsto_pow_totalDegree_mul_eval
    {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℂ) {a : ι → ℂ → ℂ} {r : ι → ℂ}
    (ha : ∀ i, Tendsto (fun z => z * a i z) (𝓝[≠] 0) (𝓝 (r i))) :
    Tendsto
      (fun z => z ^ P.totalDegree * MvPolynomial.eval (fun i => a i z) P)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval r
        (MvPolynomial.homogeneousComponent P.totalDegree P))) := by
  classical
  let D := P.totalDegree
  have hz : Tendsto (fun z : ℂ => z) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hterm : ∀ d ∈ Finset.range (D + 1),
      Tendsto
        (fun z => z ^ (D - d) *
          MvPolynomial.eval (fun i => z * a i z)
            (MvPolynomial.homogeneousComponent d P))
        (𝓝[≠] 0)
        (𝓝 (if d = D then
          MvPolynomial.eval r (MvPolynomial.homogeneousComponent D P) else 0)) := by
    intro d hd
    have hpoly := tendsto_mvPolynomial_eval ha
      (MvPolynomial.homogeneousComponent d P)
    by_cases hdD : d = D
    · subst d
      simpa using hpoly
    · have hlt : d < D := lt_of_le_of_ne
          (Nat.le_of_lt_succ (Finset.mem_range.mp hd)) hdD
      have hpow : Tendsto (fun z : ℂ => z ^ (D - d)) (𝓝[≠] 0) (𝓝 0) := by
        simpa [zero_pow (Nat.sub_pos_of_lt hlt).ne'] using hz.pow (D - d)
      simpa [hdD] using hpow.mul hpoly
  have hsum := tendsto_finsetSum (s := Finset.range (D + 1)) fun d hd => hterm d hd
  have hlimsum :
      (∑ d ∈ Finset.range (D + 1),
        (if d = D then
          MvPolynomial.eval r (MvPolynomial.homogeneousComponent D P) else 0)) =
        MvPolynomial.eval r (MvPolynomial.homogeneousComponent D P) := by
    rw [Finset.sum_eq_single D]
    · simp
    · intro d hd hne
      simp [hne]
    · simp
  rw [hlimsum] at hsum
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun z =>
    (pow_totalDegree_mul_eval_eq_sum_homogeneousComponent P (fun i => a i z) z).symm

def gammaSimpleZeroCovariantJet (branch k : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch) z /
    gammaPoleSimpleZeroSection branch z

def gammaSimpleZeroBoundaryResidueValue (branch n : ℕ) : Fin (n + 1) → ℂ :=
  Fin.cases 1 fun j =>
    iteratedDeriv (j.val + 2) (gammaPoleSimpleZeroSection branch) 0 /
      deriv (gammaPoleSimpleZeroSection branch) 0

theorem tendsto_scale_gammaSimpleZeroCovariantJet (branch k : ℕ) :
    Tendsto (fun z => z * gammaSimpleZeroCovariantJet branch k z)
      (𝓝[≠] 0)
      (𝓝 (iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch) 0 /
        deriv (gammaPoleSimpleZeroSection branch) 0)) := by
  have hUan := gammaPoleRegularUnit_analyticAt_zero branch
  have hS : AnalyticAt ℂ (gammaPoleSimpleZeroSection branch) 0 := by
    unfold gammaPoleSimpleZeroSection
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => -z) 0) |>.mul
      (hUan.inv (by rw [gammaPoleRegularUnit_zero]; exact one_ne_zero))
  have hDan : AnalyticAt ℂ
      (iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch)) 0 :=
    analyticAt_iteratedDeriv_of_analyticAt hS (k + 1)
  have hlim : Tendsto
      (fun z => -iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch) z *
        gammaPoleRegularUnit branch z)
      (𝓝[≠] 0)
      (𝓝 (iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch) 0 /
        deriv (gammaPoleSimpleZeroSection branch) 0)) := by
    convert! (hDan.continuousAt.neg.mul hUan.continuousAt).tendsto.mono_left
      inf_le_left using 1
    apply congrArg nhds
    change iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch) 0 /
        deriv (gammaPoleSimpleZeroSection branch) 0 =
      -iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch) 0 *
        gammaPoleRegularUnit branch 0
    rw [gammaPoleRegularUnit_zero, deriv_gammaPoleSimpleZeroSection_zero]
    ring
  apply hlim.congr'
  have hUne : ∀ᶠ z : ℂ in 𝓝[≠] 0, gammaPoleRegularUnit branch z ≠ 0 :=
    nhdsWithin_le_nhds (hUan.continuousAt.eventually_ne (by
      rw [gammaPoleRegularUnit_zero]
      exact one_ne_zero))
  filter_upwards [self_mem_nhdsWithin, hUne] with z hz hUz
  unfold gammaSimpleZeroCovariantJet gammaPoleSimpleZeroSection
  field_simp [hz, hUz]
  rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hz, mul_one]

theorem tendsto_scale_gammaSimpleZeroBoundaryCoordinates (branch n : ℕ) :
    ∀ i : Fin (n + 1),
      Tendsto (fun z => z * gammaSimpleZeroCovariantJet branch i.val z)
        (𝓝[≠] 0) (𝓝 (gammaSimpleZeroBoundaryResidueValue branch n i)) := by
  intro i
  induction i using Fin.cases with
  | zero =>
      simpa [gammaSimpleZeroBoundaryResidueValue, iteratedDeriv_one,
        gammaSimpleZeroCovariantJet, deriv_gammaPoleSimpleZeroSection_zero] using
        tendsto_scale_gammaSimpleZeroCovariantJet branch 0
  | succ j =>
      simpa [gammaSimpleZeroBoundaryResidueValue, gammaSimpleZeroCovariantJet,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        tendsto_scale_gammaSimpleZeroCovariantJet branch (j.val + 1)

def gammaSimpleZeroCovariantEval (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval (fun i => gammaSimpleZeroCovariantJet branch i.val z) P

theorem meromorphicAt_gammaSimpleZeroCovariantJet (branch k : ℕ) :
    MeromorphicAt (gammaSimpleZeroCovariantJet branch k) 0 := by
  have hUan := gammaPoleRegularUnit_analyticAt_zero branch
  have hS : AnalyticAt ℂ (gammaPoleSimpleZeroSection branch) 0 := by
    unfold gammaPoleSimpleZeroSection
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => -z) 0) |>.mul
      (hUan.inv (by rw [gammaPoleRegularUnit_zero]; exact one_ne_zero))
  have hD : AnalyticAt ℂ
      (iteratedDeriv (k + 1) (gammaPoleSimpleZeroSection branch)) 0 :=
    analyticAt_iteratedDeriv_of_analyticAt hS (k + 1)
  exact hD.meromorphicAt.div hS.meromorphicAt

theorem meromorphicAt_gammaSimpleZeroCovariantEval (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MeromorphicAt (gammaSimpleZeroCovariantEval branch n P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have heq : gammaSimpleZeroCovariantEval branch n (MvPolynomial.C a) =
          fun _ : ℂ => a := by
        funext z
        simp [gammaSimpleZeroCovariantEval]
      rw [heq]
      exact MeromorphicAt.const a (0 : ℂ)
  | add P Q hP hQ =>
      have heq : gammaSimpleZeroCovariantEval branch n (P + Q) =
          gammaSimpleZeroCovariantEval branch n P +
            gammaSimpleZeroCovariantEval branch n Q := by
        funext z
        simp [gammaSimpleZeroCovariantEval]
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : gammaSimpleZeroCovariantEval branch n (P * MvPolynomial.X i) =
          gammaSimpleZeroCovariantEval branch n P *
            gammaSimpleZeroCovariantJet branch i.val := by
        funext z
        simp [gammaSimpleZeroCovariantEval]
      rw [heq]
      exact hP.mul (meromorphicAt_gammaSimpleZeroCovariantJet branch i.val)

theorem tendsto_gammaSimpleZeroCovariantEval_topResidue (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    Tendsto
      (fun z => z ^ P.totalDegree * gammaSimpleZeroCovariantEval branch n P z)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
        (MvPolynomial.homogeneousComponent P.totalDegree P))) := by
  exact tendsto_pow_totalDegree_mul_eval P
    (tendsto_scale_gammaSimpleZeroBoundaryCoordinates branch n)

theorem meromorphicOrderAt_gammaSimpleZeroCovariantEval
    (branch n : ℕ) {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hres : MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
      (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0) :
    meromorphicOrderAt (gammaSimpleZeroCovariantEval branch n P) 0 =
      ((-(P.totalDegree : ℤ) : ℤ) : WithTop ℤ) := by
  apply meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul P.totalDegree
    (meromorphicAt_gammaSimpleZeroCovariantEval branch n P) hres
  simpa using tendsto_gammaSimpleZeroCovariantEval_topResidue branch n P

def gammaSimpleZeroBoundaryResidueGerm (n : ℕ) : Fin (n + 1) → NatGerm :=
  Fin.cases 1 fun j => gammaSimpleZeroCovariantResidueGerm j.val

theorem gammaSimpleZeroBoundaryResidueGerm_eq_aeval (n : ℕ) :
    gammaSimpleZeroBoundaryResidueGerm n = fun i =>
      MvPolynomial.aeval
        (fun j : Fin n => gammaSimpleZeroCovariantResidueGerm j.val)
        (HTGeometry.simpleZeroBoundaryResidue n i) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [gammaSimpleZeroBoundaryResidueGerm,
      HTGeometry.simpleZeroBoundaryResidue]
  | succ j => simp [gammaSimpleZeroBoundaryResidueGerm,
      HTGeometry.simpleZeroBoundaryResidue]

theorem aeval_gammaSimpleZeroBoundaryResidueGerm (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.aeval (gammaSimpleZeroBoundaryResidueGerm n) P =
      MvPolynomial.aeval
        (fun j : Fin n => gammaSimpleZeroCovariantResidueGerm j.val)
        (HTGeometry.simpleZeroDehomogenize n P) := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+* NatGerm :=
    (MvPolynomial.aeval (gammaSimpleZeroBoundaryResidueGerm n)).toRingHom
  let rhs : MvPolynomial (Fin (n + 1)) ℂ →+* NatGerm := (MvPolynomial.aeval
      (fun j : Fin n => gammaSimpleZeroCovariantResidueGerm j.val)).toRingHom.comp
    (HTGeometry.simpleZeroDehomogenize n)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, HTGeometry.simpleZeroDehomogenize]
    · intro i
      rw [show lhs (MvPolynomial.X i) = gammaSimpleZeroBoundaryResidueGerm n i by
        simp [lhs]]
      rw [gammaSimpleZeroBoundaryResidueGerm_eq_aeval]
      simp [rhs, HTGeometry.simpleZeroDehomogenize]
  exact RingHom.congr_fun hhom P

theorem gammaSimpleZeroTopResidueGerm_ne_zero
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP0 : P ≠ 0) :
    MvPolynomial.aeval (gammaSimpleZeroBoundaryResidueGerm n)
      (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := by
  rw [aeval_gammaSimpleZeroBoundaryResidueGerm]
  have hAI : AlgebraicIndependent ℂ
      (fun j : Fin n => gammaSimpleZeroCovariantResidueGerm j.val) :=
    algebraicIndependent_gammaSimpleZeroCovariantResidueGerm.comp Fin.val Fin.val_injective
  have hdehom : HTGeometry.simpleZeroDehomogenize n
      (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 :=
    HTGeometry.simpleZeroDehomogenize_ne_zero_of_isHomogeneous
    (MvPolynomial.homogeneousComponent_isHomogeneous P.totalDegree P)
    (HTGeometry.homogeneousComponent_totalDegree_ne_zero hP0)
  have hne := (algebraicIndependent_iff_injective_aeval.mp hAI).ne hdehom
  simpa using hne

theorem gammaSimpleZeroBoundaryResidueGerm_eq_sequence (n : ℕ) :
    gammaSimpleZeroBoundaryResidueGerm n = fun i =>
      (fun N : ℕ => gammaSimpleZeroBoundaryResidueValue (N - 1) n i : NatGerm) := by
  funext i
  induction i using Fin.cases with
  | zero =>
      change (↑(fun _ : ℕ => (1 : ℂ)) : NatGerm) =
        ↑(fun N : ℕ => gammaSimpleZeroBoundaryResidueValue (N - 1) n 0)
      rw [Filter.Germ.coe_eq]
      exact Filter.Eventually.of_forall fun N => by
        simp [gammaSimpleZeroBoundaryResidueValue]
  | succ j =>
      change (↑(fun N : ℕ =>
          iteratedDeriv (j.val + 2) (reciprocalGammaFactorialZoom (N - 1)) 0 /
            deriv (reciprocalGammaFactorialZoom (N - 1)) 0) : NatGerm) =
        ↑(fun N : ℕ => gammaSimpleZeroBoundaryResidueValue (N - 1) n j.succ)
      rw [Filter.Germ.coe_eq]
      exact Filter.Eventually.of_forall fun N => by
        simp only [gammaSimpleZeroBoundaryResidueValue, Fin.cases_succ]
        have hderiv : deriv (gammaPoleSimpleZeroSection (N - 1)) 0 =
            deriv (reciprocalGammaFactorialZoom (N - 1)) 0 := by
          rw [← iteratedDeriv_one, ← iteratedDeriv_one,
            gammaPoleSimpleZeroSection_iteratedDeriv_eq_zoom 1 (N - 1)]
        rw [gammaPoleSimpleZeroSection_iteratedDeriv_eq_zoom (j.val + 2) (N - 1),
          hderiv]

/-- Every nonzero top homogeneous boundary trace is detected arbitrarily far along the genuine
reciprocal-Gamma zero-branch tower. -/
theorem exists_cofinal_gammaSimpleZero_topResidue_ne_zero
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP0 : P ≠ 0) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
        (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := by
  let Q := MvPolynomial.homogeneousComponent P.totalDegree P
  let x : Fin (n + 1) → ℕ → ℂ := fun i N =>
    gammaSimpleZeroBoundaryResidueValue (N - 1) n i
  have hsequence :
      ((mvPolynomialSequenceEval x Q : ℕ → ℂ) : NatGerm) ≠ 0 := by
    rw [← aeval_sequenceGerm_eq x Q]
    have hx : (fun i => (x i : NatGerm)) = gammaSimpleZeroBoundaryResidueGerm n := by
      exact (gammaSimpleZeroBoundaryResidueGerm_eq_sequence n).symm
    rw [hx]
    exact gammaSimpleZeroTopResidueGerm_ne_zero hP0
  by_contra hdetect
  simp only [not_exists, not_and, not_not] at hdetect
  apply hsequence
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨B + 1, fun N hN => by
    rw [mvPolynomialSequenceEval_apply]
    exact hdetect (N - 1) (by omega)⟩

/-- The full analytic order law occurs cofinally: every nonzero covariant observable realizes
pole order equal to minus its total degree on arbitrarily remote reciprocal-Gamma branches. -/
theorem exists_cofinal_meromorphicOrderAt_gammaSimpleZeroCovariantEval
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP0 : P ≠ 0) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt (gammaSimpleZeroCovariantEval branch n P) 0 =
        ((-(P.totalDegree : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨branch, hbranch, hres⟩ :=
    exists_cofinal_gammaSimpleZero_topResidue_ne_zero hP0 B
  exact ⟨branch, hbranch,
    meromorphicOrderAt_gammaSimpleZeroCovariantEval branch n hres⟩

/-- A finite normalized `k`th-pole limit, zero or nonzero, bounds meromorphic order below by
`-k`.  The nonzero case is exact; a zero limit means that cancellation has raised the order. -/
theorem neg_nat_le_meromorphicOrderAt_of_tendsto_pow_mul
    {f : ℂ → ℂ} {p c : ℂ} (k : ℕ) (hf : MeromorphicAt f p)
    (hlim : Tendsto (fun z : ℂ => (z - p) ^ k * f z) (𝓝[≠] p) (𝓝 c)) :
    ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  by_cases hc : c = 0
  · subst c
    have hpow : MeromorphicAt (fun z : ℂ => (z - p) ^ k) p := by fun_prop
    have hprod : MeromorphicAt (fun z : ℂ => (z - p) ^ k * f z) p := hpow.mul hf
    have hpos : 0 < meromorphicOrderAt (fun z : ℂ => (z - p) ^ k * f z) p :=
      (tendsto_zero_iff_meromorphicOrderAt_pos hprod).mp hlim
    change meromorphicOrderAt ((fun z : ℂ => (z - p) ^ k) * f) p > 0 at hpos
    rw [meromorphicOrderAt_mul hpow hf] at hpos
    have hpowOrder : meromorphicOrderAt (fun z : ℂ => (z - p) ^ k) p =
        ((k : ℤ) : WithTop ℤ) := by
      simpa only using!
        (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := p) (n := k))
    rw [hpowOrder] at hpos
    by_cases htop : meromorphicOrderAt f p = ⊤
    · simp [htop]
    · lift meromorphicOrderAt f p to ℤ using htop with q hq
      have hposInt : (0 : ℤ) < (k : ℤ) + q := by exact_mod_cast hpos
      exact_mod_cast (show -(k : ℤ) ≤ q by omega)
  · rw [meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul k hf hc hlim]

def GammaSimpleZeroCovariantTowerPoleCutoff (n r : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) : Prop :=
  ∀ branch : ℕ, ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (gammaSimpleZeroCovariantEval branch n P) 0

/-- **Full holographic Fock-filtration law.**  At every finite jet height and every pole cutoff,
the reciprocal-Gamma covariant tower filtration is exactly polynomial particle number. -/
theorem gammaSimpleZeroCovariantTowerPoleCutoff_iff
    {n r : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    GammaSimpleZeroCovariantTowerPoleCutoff n r P ↔ P.totalDegree ≤ r := by
  constructor
  · intro hH
    by_cases hP0 : P = 0
    · simp [hP0]
    · obtain ⟨branch, _, horder⟩ :=
        exists_cofinal_meromorphicOrderAt_gammaSimpleZeroCovariantEval hP0 0
      have hbound := hH branch
      rw [horder] at hbound
      have hboundInt : -(r : ℤ) ≤ -(P.totalDegree : ℤ) := by
        exact_mod_cast hbound
      have hdegreeInt : (P.totalDegree : ℤ) ≤ r := by omega
      exact_mod_cast hdegreeInt
  · intro hdeg branch
    have horderD : ((-(P.totalDegree : ℤ) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (gammaSimpleZeroCovariantEval branch n P) 0 := by
      apply neg_nat_le_meromorphicOrderAt_of_tendsto_pow_mul P.totalDegree
        (meromorphicAt_gammaSimpleZeroCovariantEval branch n P)
      simpa using tendsto_gammaSimpleZeroCovariantEval_topResidue branch n P
    have hcutInt : -(r : ℤ) ≤ -(P.totalDegree : ℤ) := by
      omega
    have hcut : ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
        ((-(P.totalDegree : ℤ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast hcutInt
    exact hcut.trans horderD

def GammaSimpleZeroCovariantTowerAtMostSimple (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) : Prop :=
  ∀ branch : ℕ, ((-1 : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (gammaSimpleZeroCovariantEval branch n P) 0

/-- **Complete analytic Gamma horizon.**  A covariant polynomial observable has at most simple
poles on the entire normalized reciprocal-Gamma zero-branch tower exactly when it is affine. -/
theorem gammaSimpleZeroCovariantTowerAtMostSimple_iff
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    GammaSimpleZeroCovariantTowerAtMostSimple n P ↔ P.totalDegree ≤ 1 := by
  constructor
  · intro hH
    by_cases hP0 : P = 0
    · simp [hP0]
    · obtain ⟨branch, _, horder⟩ :=
        exists_cofinal_meromorphicOrderAt_gammaSimpleZeroCovariantEval hP0 0
      have hbound := hH branch
      rw [horder] at hbound
      have hboundInt : (-(1 : ℤ)) ≤ -(P.totalDegree : ℤ) := by
        exact_mod_cast hbound
      have hdegreeInt : (P.totalDegree : ℤ) ≤ 1 := by omega
      exact_mod_cast hdegreeInt
  · intro hdeg branch
    by_cases hP0 : P = 0
    · subst P
      have heq : gammaSimpleZeroCovariantEval branch n 0 = 0 := by
        funext z
        simp [gammaSimpleZeroCovariantEval]
      rw [heq]
      simp
    have hD : P.totalDegree = 0 ∨ P.totalDegree = 1 := by omega
    rcases hD with hD | hD
    · have hPC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hD
      have hc : MvPolynomial.coeff 0 P ≠ 0 := by
        intro hc
        apply hP0
        rw [hPC, hc, map_zero]
      rw [hPC]
      have heq : gammaSimpleZeroCovariantEval branch n
          (MvPolynomial.C (MvPolynomial.coeff 0 P)) =
          fun _ : ℂ => MvPolynomial.coeff 0 P := by
        funext z
        simp [gammaSimpleZeroCovariantEval]
      rw [heq]
      have hnonneg : 0 ≤ meromorphicOrderAt
          (fun _ : ℂ => MvPolynomial.coeff 0 P) 0 :=
        (by fun_prop : AnalyticAt ℂ
          (fun _ : ℂ => MvPolynomial.coeff 0 P) 0).meromorphicOrderAt_nonneg
      exact (show ((-1 : ℤ) : WithTop ℤ) ≤ (0 : ℤ) by exact_mod_cast
        (show (-1 : ℤ) ≤ 0 by omega)) |>.trans hnonneg
    · let c := MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
          (MvPolynomial.homogeneousComponent P.totalDegree P)
      by_cases hc : c = 0
      · have hlim : Tendsto
            (fun z => (z - 0) * gammaSimpleZeroCovariantEval branch n P z)
            (𝓝[≠] 0) (𝓝 0) := by
          have hlimit := tendsto_gammaSimpleZeroCovariantEval_topResidue branch n P
          have hc' : MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
              (MvPolynomial.homogeneousComponent 1 P) = 0 := by
            simpa [c, hD] using hc
          rw [hD, hc'] at hlimit
          simpa using hlimit
        have hnonneg := meromorphicOrderAt_nonneg_of_tendsto_mul_sub_zero
          (meromorphicAt_gammaSimpleZeroCovariantEval branch n P) hlim
        exact (show ((-1 : ℤ) : WithTop ℤ) ≤ (0 : ℤ) by exact_mod_cast
          (show (-1 : ℤ) ≤ 0 by omega)) |>.trans hnonneg
      · have hres : MvPolynomial.eval
            (gammaSimpleZeroBoundaryResidueValue branch n)
            (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := hc
        rw [meromorphicOrderAt_gammaSimpleZeroCovariantEval branch n hres, hD]
        exact le_rfl

/-- Pointwise Bell conjugacy for an arbitrary analytic nonvanishing section. -/
theorem eval_bellCoefficientMap_logDeriv_eq_covariant
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hf0 : f z ≠ 0)
    (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval
        (fun i : Fin (n + 1) =>
          iteratedDeriv i.val (fun w => deriv f w / f w) z)
        (bellCoefficientMap n Q) =
      MvPolynomial.eval
        (fun i : Fin (n + 1) => iteratedDeriv (i.val + 1) f z / f z) Q := by
  have hev : {w : ℂ | AnalyticAt ℂ f w ∧ f w ≠ 0} ∈ 𝓝 z :=
    Filter.inter_mem hf.eventually_analyticAt (hf.continuousAt.eventually_ne hf0)
  obtain ⟨Ω, hΩsub, hΩopen, hzΩ⟩ := mem_nhds_iff.mp hev
  rw [eval_bellCoefficientMap]
  apply congrArg (fun v : Fin (n + 1) → ℂ => MvPolynomial.eval v Q)
  funext i
  rw [bellAt, MvPolynomial.eval_rename]
  have hbell := iteratedDeriv_eq_bellCore_generic hΩopen
    (fun w hw => (hΩsub hw).1) (fun w hw => (hΩsub hw).2)
      (i.val + 1) hzΩ
  rw [hbell]
  field_simp [hf0]
  congr 1

def gammaSimpleZeroRawJetEval (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun i : Fin (n + 1) =>
      iteratedDeriv i.val
        (fun w => deriv (gammaPoleSimpleZeroSection branch) w /
          gammaPoleSimpleZeroSection branch w) z) P

theorem gammaSimpleZeroRawJetEval_eventuallyEq_covariant (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    gammaSimpleZeroRawJetEval branch n P =ᶠ[𝓝[≠] 0]
      gammaSimpleZeroCovariantEval branch n ((HTGeometry.bellCoefficientEquiv n).symm P) := by
  have hUan := gammaPoleRegularUnit_analyticAt_zero branch
  have hS0 : AnalyticAt ℂ (gammaPoleSimpleZeroSection branch) 0 := by
    unfold gammaPoleSimpleZeroSection
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => -z) 0) |>.mul
      (hUan.inv (by rw [gammaPoleRegularUnit_zero]; exact one_ne_zero))
  have hUne : ∀ᶠ z : ℂ in 𝓝[≠] 0, gammaPoleRegularUnit branch z ≠ 0 :=
    nhdsWithin_le_nhds (hUan.continuousAt.eventually_ne (by
      rw [gammaPoleRegularUnit_zero]
      exact one_ne_zero))
  have hSan : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      AnalyticAt ℂ (gammaPoleSimpleZeroSection branch) z :=
    nhdsWithin_le_nhds hS0.eventually_analyticAt
  filter_upwards [self_mem_nhdsWithin, hUne, hSan] with z hz hUz hSz
  have hSzne : gammaPoleSimpleZeroSection branch z ≠ 0 := by
    unfold gammaPoleSimpleZeroSection
    exact mul_ne_zero (neg_ne_zero.mpr hz) (inv_ne_zero hUz)
  let Q := (HTGeometry.bellCoefficientEquiv n).symm P
  have hBell := eval_bellCoefficientMap_logDeriv_eq_covariant hSz hSzne n Q
  have hmap : bellCoefficientMap n Q = P := by
    rw [← HTGeometry.bellCoefficientEquiv_apply,
      RingEquiv.apply_symm_apply]
  rw [hmap] at hBell
  simpa [gammaSimpleZeroRawJetEval, gammaSimpleZeroCovariantEval,
    gammaSimpleZeroCovariantJet, Q] using hBell

def GammaSimpleZeroRawTowerPoleCutoff (n r : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) : Prop :=
  ∀ branch : ℕ, ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (gammaSimpleZeroRawJetEval branch n P) 0

/-- **Full raw holographic Fock-filtration law.**  In connected/logarithmic-derivative
coordinates, every pole cutoff is the Bell image of the matching covariant particle-number
cutoff. -/
theorem gammaSimpleZeroRawTowerPoleCutoff_iff_exists_bellDegree
    {n r : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    GammaSimpleZeroRawTowerPoleCutoff n r P ↔
      ∃ Q : MvPolynomial (Fin (n + 1)) ℂ,
        Q.totalDegree ≤ r ∧ bellCoefficientMap n Q = P := by
  have hpred : GammaSimpleZeroRawTowerPoleCutoff n r P ↔
      GammaSimpleZeroCovariantTowerPoleCutoff n r
        ((HTGeometry.bellCoefficientEquiv n).symm P) := by
    constructor <;> intro h branch
    · rw [← meromorphicOrderAt_congr
          (gammaSimpleZeroRawJetEval_eventuallyEq_covariant branch n P)]
      exact h branch
    · rw [meromorphicOrderAt_congr
          (gammaSimpleZeroRawJetEval_eventuallyEq_covariant branch n P)]
      exact h branch
  rw [hpred, gammaSimpleZeroCovariantTowerPoleCutoff_iff]
  constructor
  · intro h
    refine ⟨(HTGeometry.bellCoefficientEquiv n).symm P, h, ?_⟩
    rw [← HTGeometry.bellCoefficientEquiv_apply, RingEquiv.apply_symm_apply]
  · rintro ⟨Q, hQ, hQP⟩
    have hQP' : HTGeometry.bellCoefficientEquiv n Q = P := by
      rwa [HTGeometry.bellCoefficientEquiv_apply]
    rw [← hQP', RingEquiv.symm_apply_apply]
    exact hQ

def GammaSimpleZeroRawTowerAtMostSimple (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) : Prop :=
  ∀ branch : ℕ, ((-1 : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (gammaSimpleZeroRawJetEval branch n P) 0

/-- **Complete raw logarithmic-jet horizon.**  A raw logarithmic-derivative differential
polynomial has at most simple poles throughout the normalized reciprocal-Gamma tower exactly
when it is the Bell image of an affine covariant polynomial. -/
theorem gammaSimpleZeroRawTowerAtMostSimple_iff_exists_bellAffine
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    GammaSimpleZeroRawTowerAtMostSimple n P ↔
      ∃ Q : MvPolynomial (Fin (n + 1)) ℂ,
        Q.totalDegree ≤ 1 ∧ bellCoefficientMap n Q = P := by
  have hpred : GammaSimpleZeroRawTowerAtMostSimple n P ↔
      GammaSimpleZeroCovariantTowerAtMostSimple n
        ((HTGeometry.bellCoefficientEquiv n).symm P) := by
    constructor <;> intro h branch
    · rw [← meromorphicOrderAt_congr
          (gammaSimpleZeroRawJetEval_eventuallyEq_covariant branch n P)]
      exact h branch
    · rw [meromorphicOrderAt_congr
          (gammaSimpleZeroRawJetEval_eventuallyEq_covariant branch n P)]
      exact h branch
  rw [hpred, gammaSimpleZeroCovariantTowerAtMostSimple_iff]
  constructor
  · intro h
    refine ⟨(HTGeometry.bellCoefficientEquiv n).symm P, h, ?_⟩
    rw [← HTGeometry.bellCoefficientEquiv_apply, RingEquiv.apply_symm_apply]
  · rintro ⟨Q, hQ, hQP⟩
    have hQP' : HTGeometry.bellCoefficientEquiv n Q = P := by
      rwa [HTGeometry.bellCoefficientEquiv_apply]
    rw [← hQP', RingEquiv.symm_apply_apply]
    exact hQ

end

end GaloisForLFunctions
