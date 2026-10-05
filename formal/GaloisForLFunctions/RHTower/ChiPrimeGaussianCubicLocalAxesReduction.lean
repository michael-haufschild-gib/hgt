import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicLocalAxisRigidity

/-!
# Removing the complete nonzero local inverse-fibre channel

Actual prime-height axes rigidity leaves only r^-2 of each complete masked
physical row in the nonzero local channel. Summing every covered label gives
a uniform bound, hence vanishing at the original cubic normalization. The
unconditional actual Schwartz family transfers the sharp signed cubic to
the full axes action. The axes saving and RH remain open.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RHTower.BAGTrace

private lemma excluded_weight_sub {P : Finset ℕ} (r : RamanujanGridPrime P)
    (x : RamanujanLocalGrid P) :
    ramanujanExcludedLocalGridWeight r x=
      ramanujanLocalGridWeight P x-ramanujanLabelledLocalGridWeight r x := by
  classical
  have he (p : RamanujanGridPrime P) :
      (if p=r then 0 else ramanujanLabelledLocalGridWeight p x)=
      ramanujanLabelledLocalGridWeight p x-(if p=r then ramanujanLabelledLocalGridWeight p x else 0) := by
    by_cases hp : p=r <;> simp [hp]
  unfold ramanujanExcludedLocalGridWeight
  simp only [he,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rfl

private lemma multiplier_band (M : ℕ) {n : ℕ} (hn : 1 < n) (hnM : n ≤ M) :
    (ramanujanDistinguishedPrimeMultiplier (Finset.range (M+1)) n : ℂ) =
      ((if n.Prime then Real.log n else 0 : ℝ) : ℂ) := by
  have h := (sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished
    (Finset.range (M+1)) (n : ℤ)).symm.trans
      (sum_ramanujanCriticalPrimeAtomWeight_fourier_range M hn hnM)
  simpa only [Int.natAbs_natCast] using h

/-- Exact prime selector after excluding one physical prime label. -/
theorem ramanujanExcludedLocalGridWeight_fourier_band (M : ℕ) (r : RamanujanBandPrime M)
    {n : ℕ} (hn : 1 < n) (hnM : n ≤ M) :
    (∑ x : RamanujanLocalGrid (Finset.range (M+1)),
      (ramanujanExcludedLocalGridWeight r x : ℂ)*
        ramanujanFourierPhase (n : ℤ) (ramanujanLocalGridNode x)) =
      if n=r.val then 0 else ((if n.Prime then Real.log n else 0 : ℝ) : ℂ) := by
  simp only [excluded_weight_sub,Complex.ofReal_sub,sub_mul,Finset.sum_sub_distrib,
    ramanujanLocalGridWeight_fourier,ramanujanLabelledLocalGridWeight_fourier,Int.natAbs_natCast]
  rw [multiplier_band M hn hnM]
  have hnC : n ∈ Finset.Icc 2 M := Finset.mem_Icc.mpr ⟨by omega,hnM⟩
  have he := ramanujanDistinguishedPrimeEntry_band M r ⟨n,hnC⟩
  change ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) r.val n=
    if n=r.val then Real.log r.val else 0 at he
  rw [he]
  by_cases hnr : n=r.val
  · subst n
    simp only [ite_true,if_pos (Finset.mem_filter.mp r.property).2,sub_self]
  · simp only [if_neg hnr,Complex.ofReal_zero,sub_zero]

private def pair_eval {P : Finset ℕ} (r : RamanujanGridPrime P) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ where
  toFun := ramanujanExcludedLocalPairAction r
  map_add' F G := by simp only [ramanujanExcludedLocalPairAction,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [ramanujanExcludedLocalPairAction,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring

private lemma pair_phase (M : ℕ) (r : RamanujanBandPrime M) {p q : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hpM : p ≤ M) (hqM : q ≤ M) (d : ℤ) :
    pair_eval r (ramanujanTripleFourierPhase ((p : ℤ),(q : ℤ),d))=
      (if p=r.val then 0 else ((if p.Prime then Real.log p else 0 : ℝ) : ℂ))*
      (if q=r.val then 0 else ((if q.Prime then Real.log q else 0 : ℝ) : ℂ)) := by
  rw [← ramanujanExcludedLocalGridWeight_fourier_band M r hp hpM,
    ← ramanujanExcludedLocalGridWeight_fourier_band M r hq hqM,Fintype.sum_mul_sum]
  simp only [pair_eval,LinearMap.coe_mk,AddHom.coe_mk,ramanujanExcludedLocalPairAction,
    ramanujanTripleFourierPhase]
  have he : ramanujanFourierPhase d 0=1 := by simp [ramanujanFourierPhase]
  simp only [he,mul_one]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Each exact full prime-height action is the original complete masked physical row. -/
theorem bagPhysicalHeightTest_primeRow {N : ℝ} (hN : 1 < N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (hr : r.val ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) :
    (Real.log r.val : ℂ)*ramanujanExcludedInverseProfileAction r
      (bagPhysicalHeightTest A (r.val : ℤ)) =
      ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
        if p=r.val ∨ q=r.val then 0 else
          ((η p*η q*η r.val : ℝ) : ℂ)*primeGaussianCubicMainEntry N p q r.val := by
  classical
  rw [← ramanujanExcludedLocalPairAction_inverse]
  change (Real.log r.val : ℂ)*pair_eval r (bagPhysicalHeightTest A (r.val : ℤ)) = _
  rw [bagPhysicalHeightTest_eq_finite hN hz A hA r hr]
  simp only [ramanujanHeightFourierTest,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  have hf : 1 ≤ ⌊N⌋₊ := by simpa using Nat.floor_mono hN.le
  have hS : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, 1 < n ∧ n ≤ ⌊2*N⌋₊ := by
    intro n hn
    exact ⟨lt_of_le_of_lt hf (Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2⟩
  unfold primeProfileBand
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpp : p.Prime
  · rw [if_pos hpp,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    rw [pair_phase _ r (hS p hp).1 (hS q hq).1 (hS p hp).2 (hS q hq).2]
    by_cases hqp : q.Prime
    · rw [if_pos hqp]
      by_cases hpr : p=r.val
      · simp [hpr]
      by_cases hqr : q=r.val
      · simp [hqr]
      rw [if_neg hpr,if_neg hqr,if_pos hpp,if_pos hqp,
        if_neg (not_or.mpr ⟨hpr,hqr⟩),bagCubicPhysicalAmplitude_nat]
      have hpL : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.log_pos (by exact_mod_cast hpp.one_lt)))
      have hqL : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.log_pos (by exact_mod_cast hqp.one_lt)))
      have hrL : (Real.log r.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.log_pos (by exact_mod_cast (Finset.mem_filter.mp r.property).2.one_lt)))
      field_simp
    · simp only [if_neg hqp,Complex.ofReal_zero,ite_self,mul_zero]
  · rw [if_neg hpp]
    apply Finset.sum_eq_zero
    intro q hq
    rw [pair_phase _ r (hS p hp).1 (hS q hq).1 (hS p hp).2 (hS q hq).2]
    simp only [if_neg hpp,Complex.ofReal_zero,ite_self,zero_mul,mul_zero]

/-- Full sum of all local nonzero inverse fibres, with every third-prime label retained. -/
def bagLocalNonzeroPrimeHeightAction (N : ℝ) (A : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  ∑ r : RamanujanBandPrime ⌊2*N⌋₊, (Real.log r.val : ℂ)*
    ramanujanLocalNonzeroAction r (bagPhysicalHeightTest A (r.val : ℤ))

/-- Full axes and intersection contribution at every labelled physical height. -/
def bagLocalAxesPrimeHeightAction (N : ℝ) (A : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  ∑ r : RamanujanBandPrime ⌊2*N⌋₊, (Real.log r.val : ℂ)*
    ramanujanLocalAxesAction r (bagPhysicalHeightTest A (r.val : ℤ))

theorem bagLocalPrimeHeightAction_split (N : ℝ) (A : SchwartzMap BAGPhysicalSpace ℂ) :
    bagLocalPrimeHeightInverseAction N A=
      bagLocalAxesPrimeHeightAction N A+bagLocalNonzeroPrimeHeightAction N A := by
  simp only [bagLocalPrimeHeightInverseAction,bagLocalAxesPrimeHeightAction,
    bagLocalNonzeroPrimeHeightAction,ramanujanExcludedInverseProfileAction_split,mul_add,
    Finset.sum_add_distrib]

private lemma height_zero {N : ℝ} {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v)
    (r : ℕ) (hr : (r : ℝ) ∉ Ioo N (2*N)) : bagPhysicalHeightTest A (r : ℤ)=0 := by
  have hz0 := hz _ hr
  have hs (ξ υ : ℝ) : bagThirdPhysicalSlice A ξ υ (r : ℝ)=0 := by
    simp [bagThirdPhysicalSlice,hA,bagCubicPhysicalAmplitude,bagCubicMellinSliceValue,hz0]
  funext x
  simp only [bagPhysicalHeightTest,Int.cast_natCast,hs,tsum_zero,mul_zero,Pi.zero_apply]

private lemma nonzero_zero {P : Finset ℕ} (r : RamanujanGridPrime P) :
    ramanujanLocalNonzeroAction r 0=0 := by
  have hi : ramanujanExcludedInverseProfileAction r 0=0 := by
    rw [← ramanujanExcludedLocalPairAction_inverse]
    simp [ramanujanExcludedLocalPairAction]
  have ha : ramanujanLocalAxesAction r 0=0 := by
    rw [ramanujanLocalAxesAction_eq]
    simp [ramanujanAxisPairAction]
  have h := ramanujanExcludedInverseProfileAction_split r 0
  simpa only [hi,ha,zero_add] using h.symm

private lemma row_norm {N : ℕ} (hN : 1 ≤ N) {η : ℝ → ℝ}
    (hη : ∀ x : ℝ, η x ∈ Icc (0 : ℝ) 1) {r : ℕ} (hr : r ∈ primeProfileBand (N : ℝ)) :
    ‖∑ p ∈ primeProfileBand (N : ℝ), ∑ q ∈ primeProfileBand (N : ℝ),
      if p=r ∨ q=r then 0 else ((η p*η q*η r : ℝ) : ℂ)*
        primeGaussianCubicMainEntry N p q r‖ ≤ 32*(N : ℝ) := by
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have he (p q : ℕ) (hp : p ∈ primeProfileBand (N : ℝ)) (hq : q ∈ primeProfileBand (N : ℝ)) :
      ‖if p=r ∨ q=r then 0 else ((η p*η q*η r : ℝ) : ℂ)*
        primeGaussianCubicMainEntry N p q r‖≤8/(N : ℝ) := by
    split_ifs
    · simp only [norm_zero]; positivity
    have hp0 := (hη (p : ℝ)).1
    have hq0 := (hη (q : ℝ)).1
    have hr0 := (hη (r : ℝ)).1
    rw [norm_mul,Complex.norm_of_nonneg (by positivity : 0≤η p*η q*η r)]
    have hpq : η p*η q≤1 :=
      (mul_le_mul (hη _).2 (hη _).2 hq0 zero_le_one).trans_eq (one_mul _)
    have hw : η p*η q*η r≤1 :=
      (mul_le_mul hpq (hη _).2 hr0 zero_le_one).trans_eq (one_mul _)
    exact (mul_le_mul hw (primeGaussianCubicMainEntry_norm_le hN hp hq hr)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _ ≤ ∑ p ∈ primeProfileBand (N : ℝ), ∑ q ∈ primeProfileBand (N : ℝ), 8/(N : ℝ) := by
      apply norm_sum_le_of_le
      intro p hp
      exact norm_sum_le_of_le _ (fun q hq => he p q hp hq)
    _ = ((primeProfileBand (N : ℝ)).card : ℝ)^2*(8/(N : ℝ)) := by simp; ring
    _ ≤ (2*(N : ℝ))^2*(8/(N : ℝ)) := by
      gcongr
      exact primeProfileBand_card_le_twice N
    _ = 32*(N : ℝ) := by field_simp; ring

/-- The COMPLETE actual nonzero local channel is uniformly bounded in the growing band. -/
theorem bagLocalNonzeroPrimeHeightAction_norm_le {N : ℕ} (hN : 1 < N)
    {η : ℝ → ℝ} (hη : ∀ x : ℝ, η x ∈ Icc (0 : ℝ) 1)
    (hz : ∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    ‖bagLocalNonzeroPrimeHeightAction N A‖≤96 := by
  classical
  have hN' : (1 : ℝ)<N := by exact_mod_cast hN
  have hN0 : (0 : ℝ)<N := by positivity
  let P := RamanujanBandPrime ⌊2*(N : ℝ)⌋₊
  have hb (r : P) : ‖(Real.log r.val : ℂ)*ramanujanLocalNonzeroAction r
      (bagPhysicalHeightTest A (r.val : ℤ))‖≤32/(N : ℝ) := by
    by_cases hr : r.val ∈ Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊2*(N : ℝ)⌋₊
    · have hrP : r.val ∈ primeProfileBand (N : ℝ) :=
        Finset.mem_filter.mpr ⟨hr,(Finset.mem_filter.mp r.property).2⟩
      have hrN := (primeProfileBand_mem hN0.le hrP).2.1
      rw [bagPhysicalHeightTest_nonzero hN' hz A hA r hr,
        show (Real.log r.val : ℂ)*((r.val : ℂ)⁻¹^2*ramanujanExcludedInverseProfileAction r
          (bagPhysicalHeightTest A (r.val : ℤ))) = (r.val : ℂ)⁻¹^2*
            ((Real.log r.val : ℂ)*ramanujanExcludedInverseProfileAction r
              (bagPhysicalHeightTest A (r.val : ℤ))) by ring,
        bagPhysicalHeightTest_primeRow hN' hz A hA r hr,norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
      calc
        _ ≤ (r.val : ℝ)⁻¹^2*(32*(N : ℝ)) :=
          mul_le_mul_of_nonneg_left (row_norm (by omega) hη hrP) (sq_nonneg _)
        _ ≤ (N : ℝ)⁻¹^2*(32*(N : ℝ)) := by gcongr
        _ = 32/(N : ℝ) := by field_simp
    · have hro : (r.val : ℝ) ∉ Ioo (N : ℝ) (2*N) := by
        intro h
        apply hr
        exact Finset.mem_Ioc.mpr ⟨Nat.floor_lt (by positivity) |>.mpr h.1,Nat.le_floor h.2.le⟩
      rw [height_zero hz A hA r.val hro,nonzero_zero,mul_zero,norm_zero]
      positivity
  have hc : (Fintype.card P : ℝ)≤3*(N : ℝ) := by
    have hcN : Fintype.card P≤⌊2*(N : ℝ)⌋₊+1 := by
      change Fintype.card ↥((Finset.range (⌊2*(N : ℝ)⌋₊+1)).filter Nat.Prime)≤_
      rw [Fintype.card_coe]
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    have hf := Nat.floor_le (by positivity : (0 : ℝ)≤2*N)
    have hcast := Nat.cast_le (α := ℝ).mpr hcN
    push_cast at hcast
    linarith
  calc
    _ ≤ ∑ r : P, 32/(N : ℝ) := norm_sum_le_of_le _ (fun r _ => hb r)
    _ = (Fintype.card P : ℝ)*(32/(N : ℝ)) := by simp
    _ ≤ (3*(N : ℝ))*(32/(N : ℝ)) := by gcongr
    _ = 96 := by field_simp; ring

private theorem log_square_limit :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 2 zero_lt_one).tendsto_div_nhds_zero
  have he : (fun x : ℝ => Real.log x^(2 : ℝ)/x^(1 : ℝ)) =
      (fun x : ℝ => (Real.log x)^2/x) := by
    funext x
    rw [show (2 : ℝ)=((2 : ℕ) : ℝ) from rfl,Real.rpow_natCast,Real.rpow_one]
  rw [he] at h
  exact h.comp tendsto_natCast_atTop_atTop

open scoped ContDiff

/-- Unconditional actual family: the entire nonzero channel vanishes at the cubic scale,
while the full axes action retains the original sharp cubic up to a vanishing error. -/
theorem exists_bagActualAxesReductionFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        primeGaussianCubicSmoothedOffDiagonal N (η N)=
          bagLocalAxesPrimeHeightAction N (A N)+bagLocalNonzeroPrimeHeightAction N (A N)) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖bagLocalNonzeroPrimeHeightAction N (A N)‖) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal N-bagLocalAxesPrimeHeightAction N (A N)‖) atTop (𝓝 0) := by
  obtain ⟨η,A,hreg,herr⟩ := exists_bagLocalPrimeHeightInverseFamily
  have hnz : Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
      ‖bagLocalNonzeroPrimeHeightAction N (A N)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun N => by positivity)) _
      (by simpa only [zero_mul] using log_square_limit.mul_const 96)
    filter_upwards [hreg,eventually_ge_atTop (2 : ℕ)] with N h hN
    exact mul_le_mul_of_nonneg_left
      (bagLocalNonzeroPrimeHeightAction_norm_le (by omega) h.2.2.1 h.2.2.2.1
        (A N) h.2.2.2.2.2.1) (by positivity)
  refine ⟨η,A,?_,hnz,?_⟩
  · filter_upwards [hreg] with N h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.trans (bagLocalPrimeHeightAction_split N (A N))⟩
  · apply squeeze_zero' (Filter.Eventually.of_forall (fun N => by positivity)) _
      (by simpa only [zero_add] using herr.add hnz)
    apply Filter.Eventually.of_forall
    intro N
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have he : primeGaussianCubicOffDiagonal N-bagLocalAxesPrimeHeightAction N (A N)=
        (primeGaussianCubicOffDiagonal N-bagLocalPrimeHeightInverseAction N (A N))+
          bagLocalNonzeroPrimeHeightAction N (A N) := by
      rw [bagLocalPrimeHeightAction_split]
      ring
    rw [he]
    exact norm_add_le _ _

end RHTower.BAGTrace
