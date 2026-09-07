import GaloisForLFunctions.RHTower.EulerDeletionReflectedChronologicalCurrent

/-!
# The reflected deletion current is a signed prefix energy

A finite weighted chronological identity retains both endpoints. At actual
zeros the endpoints decay, exposing the literal positive prefix energy and
its strict orientation by horizontal displacement.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionReflectedEnergy
open DeletionReflectedGram DeletionReflectedCurrent DeletionChronologicalLimit
open DeletionJointCirculation

/-- The real exponent by which critical-line reflection changes the literal jumps. -/
def exponent (s : ℂ) : ℝ := 2*s.re-1

/-- The actual positive weight relating reflected jumps at the same integer. -/
def weight (s : ℂ) (n : ℕ) : ℝ := ((n:ℝ)+1)^(exponent s)

/-- Literal prefix-energy contribution of one weight increment. -/
def energyTerm (p : ℕ) (s : ℂ) (n : ℕ) : ℝ :=
  (weight s (n+1)-weight s n)*‖endpoint (eulerDeletionWeightedJump p s) (n+1)‖^2

private theorem endpoint_succ (u : ℕ → ℂ) (N : ℕ) :
    endpoint u (N+1)=endpoint u N+u N := Finset.sum_range_succ _ _

private theorem cross_succ (u v : ℕ → ℂ) (N : ℕ) :
    chronologicalCrossPrefix u v (N+1)=chronologicalCrossPrefix u v N+
      endpoint u N*star (v N) := Finset.sum_range_succ _ _

private theorem norm_square_cast (z : ℂ) : ((‖z‖^2:ℝ):ℂ)=z*star z := by
  simpa only [Complex.ofReal_pow, Complex.star_def] using (Complex.mul_conj' z).symm

/-- The full complex weighted chronology is a prefix energy plus exact terminal terms. -/
theorem weighted_cross_identity (w : ℕ → ℝ) (u : ℕ → ℂ) (N : ℕ) :
    chronologicalCrossPrefix u (fun n => (w n:ℂ)*u n) N-
      chronologicalCrossPrefix (fun n => (w n:ℂ)*u n) u N =
      (w N:ℂ)*((‖endpoint u N‖^2:ℝ):ℂ)-
        endpoint (fun n => (w n:ℂ)*u n) N*star (endpoint u N)-
        ∑ n ∈ Finset.range N, (((w (n+1)-w n)*‖endpoint u (n+1)‖^2:ℝ):ℂ) := by
  induction N with
  | zero => simp [chronologicalCrossPrefix, endpoint]
  | succ N ih =>
    rw [cross_succ, cross_succ, Finset.sum_range_succ]
    simp only [endpoint_succ, Complex.ofReal_mul, Complex.ofReal_sub, norm_square_cast,
      Complex.star_def, map_add, map_mul, Complex.conj_ofReal] at ih ⊢
    linear_combination ih

/-- Reflection is the actual real weight change, with all phases and coefficients retained. -/
theorem reflected_jump_eq_weight (p n : ℕ) (s : ℂ) :
    eulerDeletionWeightedJump p (partner s) n=
      (weight s n:ℂ)*eulerDeletionWeightedJump p s n := by
  have hx : 0<(n:ℝ)+1 := by positivity
  have hn : (((n:ℝ)+1:ℝ):ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have he : (exponent s:ℂ)+(-s)= -partner s := by
    apply Complex.ext
    · simp [exponent, partner]
      ring
    · simp [exponent, partner]
  change eulerDeletionDirichletCoefficient p n*(((n:ℝ)+1:ℝ):ℂ)^(-partner s) =
    (weight s n:ℂ)*(eulerDeletionDirichletCoefficient p n*(((n:ℝ)+1:ℝ):ℂ)^(-s))
  rw [weight, Complex.ofReal_cpow hx.le]
  calc
    _ = eulerDeletionDirichletCoefficient p n*
      ((((n:ℝ)+1:ℝ):ℂ)^(exponent s:ℂ)*(((n:ℝ)+1:ℝ):ℂ)^(-s)) := by
        rw [← Complex.cpow_add _ _ hn, he]
    _ = _ := by ring

/-- Actual finite source energy identity, including every incomplete cutoff and both endpoints. -/
theorem source_energy_identity (p N : ℕ) (s : ℂ) :
    reflectedCross p p s N-reflectedCross p p (partner s) N =
      ((weight s N*‖endpoint (eulerDeletionWeightedJump p s) N‖^2:ℝ):ℂ)-
        endpoint (eulerDeletionWeightedJump p (partner s)) N*
          star (endpoint (eulerDeletionWeightedJump p s) N)-
        ((∑ n ∈ Finset.range N, energyTerm p s n):ℝ) := by
  have hv : (fun n => (weight s n:ℂ)*eulerDeletionWeightedJump p s n)=
      eulerDeletionWeightedJump p (partner s) := by
    funext n
    exact (reflected_jump_eq_weight p n s).symm
  have h := weighted_cross_identity (weight s) (eulerDeletionWeightedJump p s) N
  rw [hv] at h
  simpa only [reflectedCross, partner_partner, energyTerm, Complex.ofReal_sum,
    Complex.ofReal_mul] using h

/-- The only amplified endpoint term still has an explicit inverse-linear bound at every zero. -/
theorem weighted_endpoint_bound (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) (N : ℕ) :
    ‖((weight rho.1 N*‖endpoint (eulerDeletionWeightedJump p rho.1) N‖^2:ℝ):ℂ)‖ ≤
      (eulerDeletionAbelTailConstant p rho.1)^2/((N:ℝ)+1) := by
  have hs := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hA : 0≤eulerDeletionAbelTailConstant p rho.1 := by
    unfold eulerDeletionAbelTailConstant
    positivity
  have hx : 0<(N:ℝ)+1 := by positivity
  have hw : 0≤weight rho.1 N := Real.rpow_nonneg hx.le _
  have hP := norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero p N hs rho.2.2.2 rho.2.1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  calc
    _ ≤ weight rho.1 N*(eulerDeletionAbelTailConstant p rho.1*((N:ℝ)+1)^(-rho.1.re))^2 := by
      apply mul_le_mul_of_nonneg_left _ hw
      exact pow_le_pow_left₀ (norm_nonneg _) hP 2
    _ = (eulerDeletionAbelTailConstant p rho.1)^2*
        (((N:ℝ)+1)^(exponent rho.1)*
          (((N:ℝ)+1)^(-rho.1.re)*((N:ℝ)+1)^(-rho.1.re))) := by unfold weight; ring
    _ = (eulerDeletionAbelTailConstant p rho.1)^2*((N:ℝ)+1)^(-1:ℝ) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 2
      unfold exponent
      ring
    _ = _ := by rw [Real.rpow_neg_one]; rfl

/-- Actual zero landing removes the amplified terminal term, without requiring critical location. -/
theorem weighted_endpoint_tendsto (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N => ((weight rho.1 N*‖endpoint (eulerDeletionWeightedJump p rho.1) N‖^2:ℝ):ℂ))
      atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => 1/((N:ℝ)+1)) atTop (nhds (0:ℝ)) := by
    simpa only [norm_kernel, Complex.one_re, Real.rpow_neg_one, one_div, norm_zero] using
      (kernel_tendsto_zero (1:ℂ) (by norm_num)).norm
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (weighted_endpoint_bound p rho))
  simpa only [mul_zero, div_eq_mul_inv, one_mul] using
    ht.const_mul ((eulerDeletionAbelTailConstant p rho.1)^2)


private theorem endpoint_at_zero (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (endpoint (eulerDeletionWeightedJump p rho.1)) atTop (nhds 0) := by
  have ht := source_endpoint_tendsto p (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
  rw [source_endpoint_value p (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
    rho.2.2.2, rho.2.1, mul_zero] at ht
  exact ht

/-- The complete source energy tends to the full complex reflected current at every actual zero. -/
theorem energy_tendsto_at_nontrivial_zero (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N => (((∑ n ∈ Finset.range N, energyTerm p rho.1 n):ℝ):ℂ)) atTop
      (nhds (reflectionCurrent p rho.1)) := by
  let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
  have hr : r.1=partner rho.1 := rfl
  have hx := endpoint_at_zero p rho
  have hy := endpoint_at_zero p r
  rw [hr] at hy
  have hd := (variationCurrent_tendsto p p (s := rho.1) (t := partner rho.1)
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
    (RiemannGaussian.NontrivialZetaZero.re_lt_one rho)
    (by rw [← hr]; exact RiemannGaussian.NontrivialZetaZero.zero_lt_re r)
    (by rw [← hr]; exact RiemannGaussian.NontrivialZetaZero.re_lt_one r)).2
  have he (N : ℕ) :
      ((weight rho.1 N*‖endpoint (eulerDeletionWeightedJump p rho.1) N‖^2:ℝ):ℂ)-
        endpoint (eulerDeletionWeightedJump p (partner rho.1)) N*
          star (endpoint (eulerDeletionWeightedJump p rho.1) N)-
        (reflectedCross p p rho.1 N-reflectedCross p p (partner rho.1) N) =
        ((∑ n ∈ Finset.range N, energyTerm p rho.1 n):ℝ) := by
    linear_combination -(source_energy_identity p N rho.1)
  have ht := ((weighted_endpoint_tendsto p rho).sub (hy.mul hx.star)).sub hd
  simpa only [star_zero, mul_zero, sub_self, zero_sub, neg_neg, reflectionCurrent] using ht.congr he

private theorem real_energy_tendsto (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, energyTerm p rho.1 n) atTop
      (nhds (reflectionCurrent p rho.1).re) := by
  have ht := (Complex.reCLM.continuous.tendsto _).comp (energy_tendsto_at_nontrivial_zero p rho)
  change Tendsto (fun N => (((∑ n ∈ Finset.range N, energyTerm p rho.1 n):ℝ):ℂ).re)
    atTop (nhds (reflectionCurrent p rho.1).re) at ht
  simpa only [Complex.ofReal_re] using ht

/-- Every term has the right-half orientation, independently of whether the parameter is a zero. -/
theorem energyTerm_nonneg (p n : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) : 0≤energyTerm p s n := by
  apply mul_nonneg _ (sq_nonneg _)
  apply sub_nonneg.mpr
  exact Real.rpow_le_rpow (by positivity) (by push_cast; linarith)
    (by unfold exponent; linarith)

/-- Every term has the left-half orientation, with the same full prefix. -/
theorem energyTerm_nonpos (p n : ℕ) {s : ℂ} (hs : s.re≤1/2) : energyTerm p s n≤0 := by
  apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  apply sub_nonpos.mpr
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith)
    (by unfold exponent; linarith)

/-- The first actual deletion prefix fixes a strict, modulus-independent nonzero energy floor. -/
theorem energyTerm_zero {p : ℕ} (hp : 0<p) (s : ℂ) :
    energyTerm p s 0=(2:ℝ)^(exponent s)-1 := by
  have hd : ¬(p+1)∣1 := by simp only [Nat.dvd_one]; omega
  simp [energyTerm, weight, endpoint, eulerDeletionWeightedJump,
    eulerDeletionDirichletCoefficient, blockDeletionCoefficient, hd]
  norm_num

/-- At a zero, the signed energy is genuinely summable, rather than a formal ordered expression. -/
theorem hasSum_energy_at_nontrivial_zero (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    HasSum (energyTerm p rho.1) (reflectionCurrent p rho.1).re := by
  have ht := real_energy_tendsto p rho
  by_cases hs : 1/2≤rho.1.re
  · exact (hasSum_iff_tendsto_nat_of_nonneg (fun n => energyTerm_nonneg p n hs) _).2 ht
  · have hn : ∀n, 0≤ -energyTerm p rho.1 n := fun n =>
      neg_nonneg.mpr (energyTerm_nonpos p n (le_of_not_ge hs))
    have htn : Tendsto (fun N => ∑ n ∈ Finset.range N, -energyTerm p rho.1 n) atTop
        (nhds (-(reflectionCurrent p rho.1).re)) := by
      simpa only [Finset.sum_neg_distrib] using ht.neg
    have hh := ((hasSum_iff_tendsto_nat_of_nonneg hn _).2 htn).neg
    simpa only [neg_neg] using hh

/-- Exact full-complex source identity: the reflected current is the real signed prefix-energy sum. -/
theorem reflectionCurrent_eq_energy (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    reflectionCurrent p rho.1=((∑' n, energyTerm p rho.1 n):ℝ) := by
  have hsum := (hasSum_energy_at_nontrivial_zero p rho).tsum_eq
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using hsum.symm
  · simpa only [Complex.ofReal_im] using reflectionCurrent_im_at_nontrivial_zero p rho

/-- The exact first-step floor persists in the full right-half source current. -/
theorem first_energy_le_current {p : ℕ} (hp : 0<p)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : 1/2≤rho.1.re) :
    (2:ℝ)^(exponent rho.1)-1 ≤ (reflectionCurrent p rho.1).re := by
  rw [← energyTerm_zero hp rho.1]
  have ht := hasSum_energy_at_nontrivial_zero p rho
  simpa only [ht.tsum_eq] using ht.summable.le_tsum 0 (fun n _ => energyTerm_nonneg p n hs)

/-- The exact first-step ceiling persists in the full left-half source current. -/
theorem current_le_first_energy {p : ℕ} (hp : 0<p)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : rho.1.re≤1/2) :
    (reflectionCurrent p rho.1).re ≤ (2:ℝ)^(exponent rho.1)-1 := by
  have ht := hasSum_energy_at_nontrivial_zero p rho
  have hn := ht.neg.summable.le_tsum 0
    (fun n _ => neg_nonneg.mpr (energyTerm_nonpos p n hs))
  rw [ht.neg.tsum_eq, energyTerm_zero hp] at hn
  linarith

/-- Every hypothetical right-half zero has strictly positive actual reflected current. -/
theorem current_re_pos_of_right {p : ℕ} (hp : 0<p)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : 1/2<rho.1.re) :
    0<(reflectionCurrent p rho.1).re := by
  have he : 0<exponent rho.1 := by unfold exponent; linarith
  have hpow : 1<(2:ℝ)^(exponent rho.1) := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) he
  exact (sub_pos.mpr hpow).trans_le (first_energy_le_current hp rho hs.le)

/-- Every hypothetical left-half zero has strictly negative actual reflected current. -/
theorem current_re_neg_of_left {p : ℕ} (hp : 0<p)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : rho.1.re<1/2) :
    (reflectionCurrent p rho.1).re<0 := by
  have he : exponent rho.1<0 := by unfold exponent; linarith
  have hpow : (2:ℝ)^(exponent rho.1)<1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) he
  exact (current_le_first_energy hp rho hs.le).trans_lt (sub_neg.mpr hpow)

/-- A nontrivial actual deletion current vanishes at a zero exactly on the critical line. -/
theorem reflectionCurrent_eq_zero_iff {p : ℕ} (hp : 0<p)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    reflectionCurrent p rho.1=0 ↔ rho.1.re=1/2 := by
  constructor
  · intro hz
    by_contra hr
    rcases lt_or_gt_of_ne hr with hleft | hright
    · have hh := current_re_neg_of_left hp rho hleft
      rw [hz, Complex.zero_re] at hh
      exact (lt_irrefl 0) hh
    · have hh := current_re_pos_of_right hp rho hright
      rw [hz, Complex.zero_re] at hh
      exact (lt_irrefl 0) hh
  · exact reflectionCurrent_of_re_half p


/-- Exact RH receiver: annihilation of the literal modulus-two reflected current at all zeros. -/
theorem riemannHypothesis_iff_modulus_two_current_zero :
    RiemannHypothesis ↔ ∀rho : RiemannGaussian.NontrivialZetaZero,
      reflectionCurrent 1 rho.1=0 := by
  constructor
  · intro hRH rho
    exact (reflectionCurrent_eq_zero_iff zero_lt_one rho).2
      (hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2)
  · intro h s hz htr hs1
    let rho : RiemannGaussian.NontrivialZetaZero := ⟨s,hz,htr,hs1⟩
    exact (reflectionCurrent_eq_zero_iff zero_lt_one rho).1 (h rho)

end RHTower.DeletionReflectedEnergy
