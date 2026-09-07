import GaloisForLFunctions.RHTower.EulerDeletionDilationPowerGrowth

/-!
# Exact logarithmic cutoff averages

Finite cutoff averaging preserves the literal compensation and the unit source
impulse. Its logarithmic taper is an exact finite identity, independent of any
experiment. Dilation separation survives arbitrary choices of the outer cutoff.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionCutoffAverage
open DeletionMobiusCurrent DeletionDilationGrowth DeletionMixedRefinement

/-- Probability weight on the integer cutoffs in `[X,M)`. -/
def logWeight (X M j : ℕ) : ℝ :=
  (Real.log (j+1 : ℕ)-Real.log j)/(Real.log M-Real.log X)

/-- Exact coefficient taper left by logarithmic cutoff averaging. -/
def taper (X M d : ℕ) : ℝ :=
  (Real.log M-Real.log (max X d : ℕ))/(Real.log M-Real.log X)

private theorem log_span_pos {X M : ℕ} (hX : 1≤X) (hXM : X<M) :
    0<Real.log M-Real.log X := by
  apply sub_pos.mpr
  exact Real.log_lt_log (by exact_mod_cast hX) (by exact_mod_cast hXM)

private theorem sum_logWeight {X M L : ℕ} (hL : L≤M) :
    (∑ j ∈ Finset.Ico L M, logWeight X M j)=
      (Real.log M-Real.log L)/(Real.log M-Real.log X) := by
  simp only [logWeight,← Finset.sum_div]
  rw [Finset.sum_Ico_eq_sub _ hL,Finset.sum_range_sub (fun j : ℕ => Real.log j) M,
    Finset.sum_range_sub (fun j : ℕ => Real.log j) L]
  simp

/-- The cutoff weights have total mass one. -/
theorem logWeight_sum {X M : ℕ} (hX : 1≤X) (hXM : X<M) :
    (∑ j ∈ Finset.Ico X M, logWeight X M j)=1 := by
  rw [sum_logWeight hXM.le,div_self (log_span_pos hX hXM).ne']

/-- Each retained cutoff has a positive logarithmic weight. -/
theorem logWeight_pos {X M j : ℕ} (hX : 1≤X) (hXM : X<M)
    (hj : j∈Finset.Ico X M) : 0<logWeight X M j := by
  apply div_pos _ (log_span_pos hX hXM)
  apply sub_pos.mpr
  exact Real.log_lt_log (by exact_mod_cast (hX.trans (Finset.mem_Ico.mp hj).1))
    (by exact_mod_cast Nat.lt_succ_self j)

/-- The suffix of the probability weights is precisely the generator taper. -/
theorem logWeight_suffix {X M d : ℕ} (hXM : X≤M) (hdM : d≤M) :
    (∑ j ∈ Finset.Ico X M, if d≤j then logWeight X M j else 0)=taper X M d := by
  rw [← Finset.sum_filter]
  have hset : (Finset.Ico X M).filter (fun j => d≤j)=Finset.Ico (max X d) M := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_Ico,max_le_iff]
    omega
  rw [hset,sum_logWeight (max_le hXM hdM)]
  rfl

/-- Averaging does not change any generator coefficient through the inner cutoff. -/
theorem taper_eq_one {X M d : ℕ} (hX : 1≤X) (hXM : X<M) (hdX : d≤X) :
    taper X M d=1 := by
  simp only [taper,max_eq_left hdX,div_self (log_span_pos hX hXM).ne']

/-- The largest endpoint coefficient vanishes exactly. -/
theorem taper_endpoint {X M : ℕ} (hXM : X≤M) : taper X M M=0 := by
  simp [taper,max_eq_right hXM]

/-- Finite summation reversal realizes the average in the original generator space. -/
theorem cutoff_sum_transfer {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {X M : ℕ} (hXM : X≤M) (f : ℕ → E) :
    (∑ j ∈ Finset.Ico X M, logWeight X M j • (∑ d ∈ Finset.Icc 1 j, f d))=
      ∑ d ∈ Finset.Icc 1 M, taper X M d • f d := by
  have hinner (j : ℕ) (hj : j∈Finset.Ico X M) :
      (∑ d ∈ Finset.Icc 1 j, f d)=
        ∑ d ∈ Finset.Icc 1 M, if d≤j then f d else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc]
    have := (Finset.mem_Ico.mp hj).2
    omega
  calc _ = ∑ j ∈ Finset.Ico X M,
        ∑ d ∈ Finset.Icc 1 M, (if d≤j then logWeight X M j else 0) • f d := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hinner j hj,Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          split_ifs <;> simp
       _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Finset.sum_smul,logWeight_suffix hXM (Finset.mem_Icc.mp hd).2]

/-- The averaged modular coordinates, with every full raw vector retained. -/
def modular (X M n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico X M, logWeight X M j*bdMobiusModularApproximant j n

/-- The harmonic compensation is averaged together with its source. -/
def harmonic (X M : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico X M, logWeight X M j*deningerHarmonicPartial j

/-- Exact tapered Möbius modular source. -/
theorem modular_eq_taper {X M : ℕ} (hXM : X≤M) (n : ℕ) :
    modular X M n= -(∑ d ∈ Finset.Icc 1 M,
      taper X M d*((ArithmeticFunction.moebius d : ℤ) : ℝ)*
        (((n%d : ℕ) : ℝ)/(d : ℝ))) := by
  have h := cutoff_sum_transfer hXM (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)*(((n%d : ℕ) : ℝ)/(d : ℝ)))
  simp only [smul_eq_mul] at h
  simp only [modular,bdMobiusModularApproximant,mul_neg,Finset.sum_neg_distrib]
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The same taper determines the compensator; no additional scalar is introduced. -/
theorem harmonic_eq_taper {X M : ℕ} (hXM : X≤M) :
    harmonic X M=∑ d ∈ Finset.Icc 1 M,
      taper X M d*(((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ)) := by
  simpa only [harmonic,deningerHarmonicPartial_eq_sum_Icc,smul_eq_mul] using
    cutoff_sum_transfer hXM (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ))

/-- The full error is exactly the average of the full raw errors at every coordinate. -/
theorem error_eq_average {X M : ℕ} (hX : 1≤X) (hXM : X<M) (n : ℕ) :
    1-modular X M n=
      ∑ j ∈ Finset.Ico X M, logWeight X M j*(1-bdMobiusModularApproximant j n) := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,logWeight_sum hX hXM,modular]

/-- The initial arithmetic defect keeps precisely the averaged harmonic scalar. -/
theorem error_initial {X M n : ℕ} (hX : 1≤X) (hXM : X<M) (hn : 1≤n) (hnX : n≤X) :
    1-modular X M n=(n : ℝ)*harmonic X M := by
  rw [error_eq_average hX hXM,harmonic,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [one_sub_bdMobiusModularApproximant j n hn
    (hnX.trans (Finset.mem_Ico.mp hj).1)]
  ring

/-- Actual finite cutoff average of the ordinary complex source prefixes. -/
def averagePrefix (X M : ℕ) (s : ℂ) (K : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico X M, (logWeight X M j : ℂ)*sourcePrefix j s K

/-- Averaging retains the initial unit impulse with a single shared scalar. -/
theorem prefix_initial {X M K : ℕ} (hX : 1≤X) (hXM : X<M) (hK : 0<K) (hKX : K≤X)
    (s : ℂ) : averagePrefix X M s K=(harmonic X M : ℂ)*rawPrefix s K-1 := by
  have hp (j : ℕ) (hj : j∈Finset.Ico X M) :
      sourcePrefix j s K=(deningerHarmonicPartial j : ℂ)*rawPrefix s K-1 := by
    rw [sourcePrefix_initial hK (hKX.trans (Finset.mem_Ico.mp hj).1) s]
    congr 2
    apply Finset.sum_congr rfl
    intro n hn
    simp [DeletionChronologicalLimit.kernel,kernel]
  unfold averagePrefix
  have havg : (∑ j ∈ Finset.Ico X M, (logWeight X M j : ℂ)*sourcePrefix j s K)=
      ∑ j ∈ Finset.Ico X M, (logWeight X M j : ℂ)*
        ((deningerHarmonicPartial j : ℂ)*rawPrefix s K-1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hp j hj]
  rw [havg]
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
  rw [← Complex.ofReal_sum,logWeight_sum hX hXM]
  simp only [Complex.ofReal_one,harmonic,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A fixed dilation exposes a defect uniformly over every larger averaging endpoint. -/
theorem exists_prefix_dilation_pair_lower {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    ∃ D K₀ : ℕ, 2≤D ∧ 1≤K₀ ∧ ∀ X M K : ℕ, 1≤X → X<M → K₀≤K → D*K≤X →
      (1 : ℝ)/8≤‖averagePrefix X M s K‖^2+‖averagePrefix X M s (D*K)‖^2 := by
  obtain ⟨D,K₀,hD,hK₀,hsep⟩ := exists_rawPrefix_dilation_separation hs hs'
  refine ⟨D,K₀,hD,hK₀,?_⟩
  intro X M K hX hXM hK hDK
  rw [prefix_initial hX hXM (by omega) (by nlinarith) s,
    prefix_initial hX hXM (by nlinarith) hDK s]
  exact scalar_pair_energy_lower (hsep K hK) _

/-- All retained initial prefixes have a linear total defect, uniformly in the outer cutoff. -/
theorem exists_prefix_square_sum_linear_lower {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    ∃ D : ℕ, 2≤D ∧ ∀ᶠ X : ℕ in atTop, ∀ M : ℕ, X<M →
      (X : ℝ)/(64*(D : ℝ))≤∑ k ∈ Finset.Icc 1 X, ‖averagePrefix X M s k‖^2 := by
  obtain ⟨D,K₀,hD,hK₀,hpair⟩ := exists_prefix_dilation_pair_lower hs hs'
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_ge_atTop (2*D*(K₀+1)),eventually_ge_atTop 1] with X hX hX1
  intro M hXM
  exact sum_prefix_lower_of_dilation_pairs (fun k => sq_nonneg _) hD hK₀ hX
    (fun K hK hDK => hpair X M K hX1 hXM hK hDK)


/-- Reciprocal-modulus deletion coefficients for the exact averaged source. -/
def averagedCoefficient (X M p : ℕ) : ℂ :=
  (taper X M (p+1) : ℂ)*DeletionMobiusCurrent.coefficient p

/-- Complete chronological current of the tapered source, including all cross terms. -/
def averagedCurrent (X M : ℕ) (s : ℂ) : ℂ :=
  DeletionMixedCurrent.quadraticCurrent (Finset.range M) (averagedCoefficient X M) s

private theorem sum_Icc_shift {E : Type*} [AddCommMonoid E] (f : ℕ → E) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, f d)=∑ p ∈ Finset.range M, f (p+1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_range_succ,ih]

/-- The tapered deletion path is the exact average of the original deletion paths. -/
theorem mixedPath_eq_average {X M : ℕ} (hXM : X≤M) (s : ℂ) (n : ℕ) :
    DeletionMixedCurrent.mixedPath (Finset.range M) (averagedCoefficient X M) s n=
      ∑ j ∈ Finset.Ico X M, (logWeight X M j : ℂ)*sourcePath j s n := by
  have h := cutoff_sum_transfer hXM (fun d => DeletionMobiusCurrent.coefficient (d-1)*
    eulerDeletionWeightedJump (d-1) s n)
  simp_rw [sum_Icc_shift] at h
  simp only [Nat.add_sub_cancel,Complex.real_smul] at h
  simpa only [DeletionMixedCurrent.mixedPath,sourcePath,averagedCoefficient,mul_assoc] using h.symm

/-- The ordinary mixed endpoint retains precisely the averaged full source prefix. -/
theorem mixedEndpoint_eq_average {X M : ℕ} (hXM : X≤M) (s : ℂ) (K : ℕ) :
    DeletionJointCirculation.endpoint
      (DeletionMixedCurrent.mixedPath (Finset.range M) (averagedCoefficient X M) s) K=
      averagePrefix X M s K := by
  simp only [DeletionJointCirculation.endpoint,mixedPath_eq_average hXM,averagePrefix,
    sourcePrefix,sourcePath,Finset.mul_sum]
  exact Finset.sum_comm

private theorem mixedHead_lower_prefix_sum {s : ℂ} (hs : 1/2<s.re) (hs' : s.re<1)
    {X M : ℕ} (hXM : X≤M) :
    DeletionReflectedEnergy.exponent s*((X : ℝ)+1)^(DeletionReflectedEnergy.exponent s-1)*
      (∑ k ∈ Finset.Icc 1 X, ‖averagePrefix X M s k‖^2)≤
        ∑ n ∈ Finset.range X,
          DeletionMixedCurrent.mixedEnergy (Finset.range M) (averagedCoefficient X M) s n := by
  rw [sum_Icc_shift,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [DeletionMixedCurrent.mixedEnergy,mixedEndpoint_eq_average hXM]
  exact mul_le_mul_of_nonneg_right (weight_increment_lower hs hs' (Finset.mem_range.mp hn))
    (sq_nonneg _)

/-- Every right-half zero forces a power floor uniformly over all outer averaging cutoffs. -/
theorem exists_averagedCurrent_rpow_lower (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2<rho.1.re) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ M : ℕ, X<M →
      C*(X : ℝ)^(2*rho.1.re-1)≤(averagedCurrent X M rho.1).re := by
  have hs0 := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hs1 := RiemannGaussian.NontrivialZetaZero.re_lt_one rho
  obtain ⟨D,hD,hbound⟩ := exists_prefix_square_sum_linear_lower hs0 hs1
  let a := DeletionReflectedEnergy.exponent rho.1
  have ha : 0<a := by dsimp [a,DeletionReflectedEnergy.exponent]; linarith
  have hDpos : (0 : ℝ)<D := by exact_mod_cast (show 0<D by omega)
  refine ⟨a/(128*(D : ℝ)),by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with X hsum hX
  intro M hXM
  have hXpos : (0 : ℝ)<X := by exact_mod_cast hX
  have htail := mixedHead_lower_prefix_sum hs hs1 hXM.le
  have hmul := mul_le_mul_of_nonneg_left (hsum M hXM)
    (show 0≤a*((X : ℝ)+1)^(a-1) by positivity)
  have hhalf : (X : ℝ)/((X : ℝ)+1)≥1/2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hX1 : (1 : ℝ)≤X := by exact_mod_cast hX
    linarith
  have hid : a*((X : ℝ)+1)^(a-1)*((X : ℝ)/(64*(D : ℝ))) =
      a/(64*(D : ℝ))*((X : ℝ)+1)^a*((X : ℝ)/((X : ℝ)+1)) := by
    rw [Real.rpow_sub_one (by positivity)]
    ring
  have hpow : (X : ℝ)^a≤((X : ℝ)+1)^a :=
    Real.rpow_le_rpow hXpos.le (by linarith) ha.le
  have hlow : a/(128*(D : ℝ))*(X : ℝ)^a≤
      a*((X : ℝ)+1)^(a-1)*((X : ℝ)/(64*(D : ℝ))) := by
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hhalf
      (show 0≤a/(64*(D : ℝ))*((X : ℝ)+1)^a by positivity)
    have hp := mul_le_mul_of_nonneg_left hpow (show 0≤a/(128*(D : ℝ)) by positivity)
    calc _ ≤ a/(128*(D : ℝ))*((X : ℝ)+1)^a := hp
         _ = a/(64*(D : ℝ))*((X : ℝ)+1)^a*(1/2) := by ring
         _ ≤ _ := hh
  have hcurrent := DeletionMixedCurrent.mixed_energy_prefix_le_current
    (Finset.range M) (averagedCoefficient X M) rho hs.le X
  exact hlow.trans (hmul.trans (htail.trans hcurrent))


/-- The exact tapered current admits adaptive outer cutoffs without losing the RH receiver. -/
theorem riemannHypothesis_iff_averagedCurrent_cofinally_subpower :
    RiemannHypothesis ↔ ∀ rho : RiemannGaussian.NontrivialZetaZero,
      ∀ e : ℝ, 0<e → ∃ B : ℝ, ∀ K : ℕ, ∃ X M : ℕ, K≤X ∧ X<M ∧
        |(averagedCurrent X M rho.1).re|≤B*(X : ℝ)^e := by
  constructor
  · intro hRH rho e he
    refine ⟨0,fun K => ⟨K,K+1,le_rfl,Nat.lt_succ_self K,?_⟩⟩
    rw [averagedCurrent,DeletionMixedCurrent.quadraticCurrent_of_re_half _ _
      (hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2)]
    simp
  · intro hupper
    have no_right (rho : RiemannGaussian.NontrivialZetaZero) (hs : 1/2<rho.1.re) : False := by
      obtain ⟨C,hC,hlow⟩ := exists_averagedCurrent_rpow_lower rho hs
      let a := 2*rho.1.re-1
      have ha : 0<a := by dsimp [a]; linarith
      obtain ⟨B,hB⟩ := hupper rho (a/2) (by linarith)
      have hg : Tendsto (fun X : ℕ => (X : ℝ)^(a/2)*C) atTop atTop :=
        ((tendsto_rpow_atTop (by linarith : 0<a/2)).comp tendsto_natCast_atTop_atTop).atTop_mul_const hC
      obtain ⟨K,hK⟩ := eventually_atTop.mp
        (hlow.and ((hg.eventually_gt_atTop B).and (eventually_ge_atTop 1)))
      obtain ⟨X,M,hKX,hXM,hup⟩ := hB K
      obtain ⟨hlo,hgt,hX1⟩ := hK X hKX
      have hXp : (0 : ℝ)<X := by exact_mod_cast hX1
      have hp : (X : ℝ)^a=(X : ℝ)^(a/2)*(X : ℝ)^(a/2) := by
        rw [← Real.rpow_add hXp]
        congr 1
        ring
      have hstrict : B*(X : ℝ)^(a/2)<C*(X : ℝ)^a := by
        rw [hp]
        have h := mul_lt_mul_of_pos_right hgt (Real.rpow_pos_of_pos hXp (a/2))
        nlinarith
      exact (not_lt_of_ge ((hlo M hXM).trans ((le_abs_self _).trans hup))) hstrict
    intro s hz ht hs1
    let rho : RiemannGaussian.NontrivialZetaZero := ⟨s,hz,ht,hs1⟩
    by_contra hr
    rcases lt_or_gt_of_ne hr with hleft | hright
    · let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
      have hre : r.1.re=1-s.re := by
        change (DeletionReflectedGram.partner s).re=1-s.re
        simp [DeletionReflectedGram.partner]
      exact no_right r (by rw [hre]; linarith)
    · exact no_right rho hright

end RHTower.DeletionCutoffAverage
