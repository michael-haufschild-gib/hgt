import GaloisForLFunctions.RHTower.WeilWorkExposingRaySublogSources
import GaloisForLFunctions.RHTower.WeilWorkExposingRaySublogArithmetic


/-!
# Derived arithmetic envelopes for actual weighted polar separators

A continuous real functional on spectral L1, applied to the actual density
weighted by `1 + log(2 + |t|)^beta`, imposes a growing multiplicative
Toeplitz ceiling on every actual polar resonator. Its primitive-set star
vectors and the prime-factor-layer harmonic theorem force an absolute
arithmetic coefficient envelope with exponent `beta + z/2`, for `1 < z < 2`.
For `0 <= beta < 1/2`, this exponent can be chosen strictly below one.

The coefficient envelope is derived from the separator, not added as a
premise. Both source poles, complex coefficients, raw atom normalization,
and the complete finite resonator tail are retained. The weighted
separator extension and exact-fibre recovery theorem remain separate;
no universal WP02 energy lower bound is asserted here.

Paper: docs/reports/weil-work/results/02-exposing-ray/SUBHALF-LOG-FIBRE-PROOF.md.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided ResonatorProfile

theorem primitive_square_of_toeplitz {b : ℕ → ℝ} {B : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hB : 0 ≤ B)
    (h : ∀ c : ℕ → ℂ, (∀ m, N < m → c m=0) →
      2*(∑ n ∈ Finset.Icc 2 N, b n*(∑ m ∈ Finset.Icc 1 N, c (n*m)*conj (c m)).re) ≤
        B*∑ m ∈ Finset.Icc 1 N, ‖c m‖^2)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 N) (hprim : WeilMeanSquare.IsPrimitiveSet S) :
    (∑ n ∈ S, b n^2) ≤ B^2 := by
  classical
  have key (t : ℝ) : 2*t*(∑ n ∈ S, b n^2) ≤ B*(1+t^2*∑ n ∈ S, b n^2) := by
    let c : ℕ → ℂ := fun m => if m=1 then 1 else if m∈S then ((t*b m : ℝ) : ℂ) else 0
    have hcN : ∀ m, N < m → c m=0 := by
      intro m hm
      have h1 : m≠1 := by omega
      have h2 : m∉S := fun h => by have := (Finset.mem_Icc.mp (hS h)).2; omega
      simp [c,h1,h2]
    have hh := h c hcN
    have hinner (n : ℕ) (hn : n∈Finset.Icc 2 N) :
        (∑ m ∈ Finset.Icc 1 N, c (n*m)*conj (c m)).re = if n∈S then t*b n else 0 := by
      obtain ⟨hn2,hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl,hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, c (n*m)*conj (c m)=0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1,hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m∈S
        · have hnm1 : n*m≠1 := by have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n*m∉S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [c,hnm1,hnmS]
        · simp [c,hm1,hmS]
      rw [hrest,add_zero,mul_one]
      have hn1 : n≠1 := by omega
      by_cases hnS : n∈S <;> simp [c,hn1,hnS]
    have hmass : (∑ m ∈ Finset.Icc 1 N, ‖c m‖^2)=1+t^2*∑ n∈S,b n^2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl,hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have hh := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega,hh.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [c,hm1,hmS]),Finset.mul_sum]
      congr 1
      · simp [c]
      · apply Finset.sum_congr rfl
        intro n hn
        have hn1 : n≠1 := by have := (Finset.mem_Icc.mp (hS hn)).1; omega
        simp [c,hn1,hn,mul_pow]
    have hlhs : (∑ n ∈ Finset.Icc 2 N, b n*(∑ m ∈ Finset.Icc 1 N,c (n*m)*conj (c m)).re)=
        t*∑ n∈S,b n^2 := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn],Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      exact Finset.sum_congr rfl fun n hn => by rw [if_pos hn]; ring
    rw [hlhs,hmass] at hh
    nlinarith only [hh]
  rcases hB.eq_or_lt with he | hp
  · have h := key 1
    rw [← he] at h
    nlinarith [Finset.sum_nonneg (fun n (_ : n∈S) => sq_nonneg (b n))]
  · have h := key (1/B)
    have he : B*(1+(1/B)^2*(∑ n∈S,b n^2)) = B+(∑ n∈S,b n^2)/B := by field_simp
    have he2 : 2*(1/B)*(∑ n∈S,b n^2)=2*((∑ n∈S,b n^2)/B) := by ring
    rw [he,he2] at h
    have hq : (∑ n∈S,b n^2)/B ≤ B := by linarith
    have hq' := (div_le_iff₀ hp).mp hq
    nlinarith only [hq']

theorem log_toeplitz_of_polar_bound {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f))
    (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ) (hc : ∀ m, N < m → c m=0) :
    2*(∑ n ∈ Finset.Icc 2 N, b n*(∑ m ∈ Finset.Icc 1 N,c (n*m)*conj (c m)).re) ≤
      (2*Real.pi*‖ell‖*(1+(Real.log N+sublogResonatorConstant)^β))*
        ∑ m ∈ Finset.Icc 1 N, ‖c m‖^2 := by
  let w : ℝ := 1 / ((N : ℝ)+1)
  let a : ℝ := Real.log N / 2 + w/4
  let f : ℝ → ℂ := resonator N c w
  have hw : 0 < w := by dsimp [w]; positivity
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNr
  have hp := paperFT_resonator_pole (N := N) (c := c) hw
  have hpol : IsPolarTest a f := by
    refine ⟨?_, contDiff_resonator N c w 2, ?_, hp.1, hp.2⟩
    · dsimp [a]; exact add_nonneg (div_nonneg (Real.log_nonneg hNr) (by norm_num)) (by positivity)
    · exact tsupport_subset_of_vanish (fun u hu =>
        sum_translates_eq_zero (fun v hv => gC_eq_zero hw hv) hu)
  have hK : N ≤ ⌊Real.exp (2*a)⌋₊ := by
    apply Nat.le_floor
    calc
      (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0).symm
      _ ≤ Real.exp (2*a) := Real.exp_le_exp.mpr (by dsimp [a]; linarith)
  have hcorr (n : ℕ) (hn : 1 ≤ n) : atomCoeff f n =
      2 * WeilWorkPBAP.resonatorMass N *
        (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)).re :=
    WeilWorkPBAP.resonator_log_sample N c hc n hn
  have htail (n : ℕ) (hn : N < n) : atomCoeff f n = 0 := by
    rw [hcorr n (by omega)]
    have hz : (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmn : N < n*m := lt_of_lt_of_le hn (Nat.le_mul_of_pos_right n (Finset.mem_Icc.mp hm).1)
      rw [hc (n*m) hmn, zero_mul]
    rw [hz, Complex.zero_re, mul_zero]
  let F : WeilTestFn := ⟨f,hpol.2.1,
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hpol.2.2.1⟩
  have hh := h F ⟨a,hpol⟩
  have hn := ell.le_opNorm (logDensityL1 hβ hβ1 F)
  have hlo := le_abs_self (ell (logDensityL1 hβ hβ1 F))
  rw [← Real.norm_eq_abs] at hlo
  have hbudget := resonator_logWeighted_mass_bound hβ hβ1 hN c hc
  have hweighted : ‖logDensityL1 hβ hβ1 F‖ ≤
      (2*Real.pi*WeilWorkPBAP.resonatorMass N*∑ m∈Finset.Icc 1 N, ‖c m‖^2)*
        (1+(Real.log N+sublogResonatorConstant)^β) := by
    rw [norm_logDensityL1]
    exact hbudget
  have hb := mul_le_mul_of_nonneg_left hweighted (norm_nonneg ell)
  have hh' := hh.trans (hlo.trans hn)
  have hh'' := hh'.trans hb
  rw [atomValue_eq_sum b hpol.2.2.1] at hh''
  change (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n*atomCoeff f n) ≤ _ at hh''
  have heq : (∑ n ∈ Finset.Icc 2 N, b n * atomCoeff f n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n * atomCoeff f n := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right hK)
    intro n hn hnot
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hlt : N < n := by
      by_contra hle; exact hnot (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
    rw [htail n hlt, mul_zero]
  rw [← heq] at hh''
  have he : (∑ n ∈ Finset.Icc 2 N, b n * atomCoeff f n) =
      WeilWorkPBAP.resonatorMass N *
        (2 * ∑ n ∈ Finset.Icc 2 N, b n *
          (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)).re) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcorr n (by have := (Finset.mem_Icc.mp hn).1; omega)]
    ring
  rw [he] at hh''
  have hprod : WeilWorkPBAP.resonatorMass N *
      (2 * ∑ n ∈ Finset.Icc 2 N, b n *
        (∑ m ∈ Finset.Icc 1 N, c (n*m) * conj (c m)).re) ≤
      WeilWorkPBAP.resonatorMass N * (2*Real.pi*‖ell‖*(1+(Real.log N+sublogResonatorConstant)^β) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖^2) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh''
  exact le_of_mul_le_mul_left hprod (WeilWorkPBAP.resonatorMass_pos N)



theorem resonator_budget_growth {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
    1+(Real.log (N:ℝ)+sublogResonatorConstant)^β ≤
      (1+sublogResonatorConstant^β)*(1+Real.log N)^β := by
  have hn := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
  have hC := one_le_sublogResonatorConstant
  have hC0 : 0 ≤ sublogResonatorConstant := by linarith
  have hL : 1 ≤ 1+Real.log (N:ℝ) := by linarith
  have hp := Real.one_le_rpow hL hβ
  have hh : Real.log (N:ℝ)+sublogResonatorConstant ≤
      sublogResonatorConstant*(1+Real.log N) := by nlinarith
  have hr := Real.rpow_le_rpow (by linarith : 0 ≤ Real.log (N:ℝ)+sublogResonatorConstant) hh hβ
  rw [Real.mul_rpow hC0 (by linarith : 0 ≤ 1+Real.log (N:ℝ))] at hr
  nlinarith only [hp,hr]

/-- Each actual polar weighted separator forces an absolute arithmetic envelope.
The envelope is derived, not an extra hypothesis on its coefficient sequence. -/
theorem exists_harmonic_envelope_of_polar_log_bound {β z : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hz : 1 < z) (hz2 : z < 2)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Icc 2 N, |b n|/Real.sqrt n) ≤ K*(1+Real.log N)^(β+z/2) := by
  obtain ⟨C,hC,harm⟩ := exists_primitive_harmonic_square_bound hz hz2
  let D := 2*Real.pi*‖ell‖*(1+sublogResonatorConstant^β)+1
  have hD : 0 < D := by
    have hp := Real.rpow_nonneg (show 0 ≤ sublogResonatorConstant by
      linarith [one_le_sublogResonatorConstant]) β
    dsimp [D]
    positivity
  refine ⟨Real.sqrt C*D,mul_pos (Real.sqrt_pos.mpr hC) hD,fun N hN => ?_⟩
  let L := 1+Real.log (N:ℝ)
  have hL : 1 ≤ L := by
    dsimp [L]
    have hh := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast (show 1≤N by omega))
    linarith
  have hL0 : 0 < L := by linarith
  let B := 2*Real.pi*‖ell‖*(1+(Real.log N+sublogResonatorConstant)^β)
  have hB : 0 ≤ B := by
    have hn := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast (show 1≤N by omega))
    have hc : 0 ≤ Real.log (N:ℝ)+sublogResonatorConstant := by
      linarith [one_le_sublogResonatorConstant]
    have hp := Real.rpow_nonneg hc β
    dsimp [B]
    positivity
  have hBD : B ≤ D*L^β := by
    have hh := mul_le_mul_of_nonneg_left (resonator_budget_growth hβ (by omega : 1≤N))
      (show 0 ≤ 2*Real.pi*‖ell‖ by positivity)
    have hp := Real.rpow_nonneg hL0.le β
    dsimp [B,D,L]
    dsimp [L] at hp
    nlinarith only [hh,hp]
  have hp (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 N) (hs : WeilMeanSquare.IsPrimitiveSet S) :
      (∑ n∈S,b n^2) ≤ (D*L^β)^2 := by
    have hh := primitive_square_of_toeplitz (by omega : 1≤N) hB
      (log_toeplitz_of_polar_bound hβ hβ1 h N (by omega)) S hS hs
    calc _ ≤ B^2 := hh
      _ ≤ (D*L^β)^2 := by nlinarith [sq_nonneg (D*L^β-B)]
  have hs := harm b (D*L^β) N hN hp
  have he : (Real.sqrt C*D*L^(β+z/2))^2 = C*(D*L^β)^2*L^z := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hC.le,Real.rpow_add hL0]
    rw [mul_pow]
    have hzpow : (L^(z/2))^2 = L^z := by
      rw [← Real.rpow_two,← Real.rpow_mul hL0.le]
      congr 1
      ring
    rw [hzpow]
    ring
  have ht : 0 ≤ Real.sqrt C*D*L^(β+z/2) := by positivity
  change (∑ n ∈ Finset.Icc 2 N, |b n|/Real.sqrt n) ≤ Real.sqrt C*D*L^(β+z/2)
  change (∑ n ∈ Finset.Icc 2 N, |b n|/Real.sqrt n)^2 ≤ C*(D*L^β)^2*L^z at hs
  rw [← he] at hs
  nlinarith only [hs,ht]

/-- Below the half-logarithmic exponent, actual separators have a strictly
sublogarithmic absolute harmonic envelope. -/
theorem exists_sublog_envelope_of_polar_log_bound {β : ℝ}
    (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ (by linarith) f)) :
    ∃ K : ℝ, 0 < K ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Icc 2 N, |b n|/Real.sqrt n) ≤ K*(1+Real.log N)^θ := by
  obtain ⟨K,hK,hbound⟩ := exists_harmonic_envelope_of_polar_log_bound hβ
    (by linarith) (z := 3/2-β) (by linarith) (by linarith) h
  exact ⟨K,hK,β+(3/2-β)/2,by linarith,by linarith,hbound⟩


end RHTower.ExposingRayTransfer
