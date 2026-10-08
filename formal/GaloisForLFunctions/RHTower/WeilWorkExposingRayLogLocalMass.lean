import GaloisForLFunctions.RHTower.WeilWorkExposingRaySublogEnvelope

/-!
# Absolute coefficient mass of actual logarithmically weighted separators

Primitive square ceilings imply an absolute mass bound `4 sqrt(N) B(N)`
for every nonnegative monotone ceiling B. Strong induction on dyadic
halves avoids an extra logarithmic loss from counting scales.

For every actual polar separator with spectral weight
`1 + log(2 + |t|)^beta`, `0 <= beta <= 1`, this gives a square-root
coefficient mass bound retaining the original exponent beta. The needed
primitive square bounds are derived from actual polar resonators.
No coefficient-growth, full-positivity, recovery or RH premise is added.
This does not itself prove one-pole recovery or the WP02 energy inequality.

Paper: docs/reports/weil-work/results/02-exposing-ray/ONE-POLE-SUBLOG-PROOF.md.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided ResonatorProfile

private theorem primitive_square_of_toeplitz {b : ℕ → ℝ} {B : ℝ} {N : ℕ}
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

/-- The full complex finite matrix bound derived from actual polar sources.
Its public form also permits positive-integer harmonic twists. -/
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



private theorem resonator_budget_growth {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
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

/-- Primitive square ceilings give square-root total absolute mass without
an extra logarithmic loss. -/
theorem sum_abs_le_four_sqrt_of_primitive {b B : ℕ → ℝ}
    (hB : ∀ N, 1 ≤ N → 0 ≤ B N)
    (hmono : ∀ M N, 1 ≤ M → M ≤ N → B M ≤ B N)
    (hprim : ∀ N, 1 ≤ N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N →
      WeilMeanSquare.IsPrimitiveSet S → (∑ n ∈ S, b n^2) ≤ (B N)^2)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, |b n|) ≤ 4*Real.sqrt N*B N := by
  have he (n : ℕ) : Finset.Ioc 1 n = Finset.Icc 2 n := by
    ext k
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  rw [← he]
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hn2 : 2 ≤ N
    · let M := N/2
      have hM : 1 ≤ M := by dsimp [M]; omega
      have hMN : M < N := Nat.div_lt_self (by omega) (by norm_num)
      let S := Finset.Ioc M N
      have hs : S ⊆ Finset.Icc 2 N := by
        intro n hn
        have hh := Finset.mem_Ioc.mp hn
        exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
      have hp : WeilMeanSquare.IsPrimitiveSet S := by
        intro m hm m' hm' k hk heq
        have hh := Finset.mem_Ioc.mp hm
        have hh' := Finset.mem_Ioc.mp hm'
        have hb := Nat.mul_le_mul hk (show M+1 ≤ m' by omega)
        dsimp [M] at hb hh'
        omega
      have hsq := hprim N hN S hs hp
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => |b n|) (fun _ => (1:ℝ))
      simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,sq_abs] at hcs
      have hcard : (S.card : ℝ) ≤ N := by
        dsimp [S]
        rw [Nat.card_Ioc]
        exact_mod_cast Nat.sub_le N M
      have hsum0 : 0 ≤ ∑ n ∈ S, b n^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hcs' := hcs.trans (mul_le_mul_of_nonneg_left hcard hsum0)
      have hbound := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg N : (0:ℝ)≤N)
      have hBN := hB N hN
      have hroot := Real.sq_sqrt (Nat.cast_nonneg N : (0:ℝ)≤N)
      have hroot0 := Real.sqrt_nonneg (N:ℝ)
      have hblock : (∑ n ∈ S, |b n|) ≤ Real.sqrt N*B N := by
        have hnon : 0 ≤ Real.sqrt (N:ℝ)*B N := mul_nonneg hroot0 hBN
        have htarget : (Real.sqrt (N:ℝ)*B N)^2 = (B N)^2*N := by rw [mul_pow,hroot]; ring
        nlinarith only [hcs',hbound,hnon,htarget]
      have hMroot := Real.sq_sqrt (Nat.cast_nonneg M : (0:ℝ)≤M)
      have hMroot0 := Real.sqrt_nonneg (M:ℝ)
      have hhalf : 2*(M:ℝ) ≤ N := by exact_mod_cast (show 2*M ≤ N by dsimp [M]; omega)
      have hroots : 4*Real.sqrt (M:ℝ) ≤ 3*Real.sqrt (N:ℝ) := by
        nlinarith only [hMroot,hroot,hMroot0,hroot0,hhalf]
      have hhead : (∑ n ∈ Finset.Ioc 1 M, |b n|) ≤ 3*Real.sqrt N*B N := by
        calc
          _ ≤ 4*Real.sqrt M*B M := ih M hMN hM
          _ ≤ 4*Real.sqrt M*B N := mul_le_mul_of_nonneg_left (hmono M N hM hMN.le) (by positivity)
          _ ≤ 3*Real.sqrt N*B N := mul_le_mul_of_nonneg_right hroots hBN
      rw [← Finset.sum_Ioc_consecutive (fun n => |b n|) hM hMN.le]
      change _ + (∑ n ∈ S, |b n|) ≤ _
      nlinarith only [hhead,hblock]
    · have hn : N=1 := by omega
      subst N
      simp only [Finset.Ioc_self,Finset.sum_empty]
      exact mul_nonneg (by positivity) (hB 1 le_rfl)

/-- Every actual weighted polar separator has square-root absolute
coefficient mass with its ORIGINAL log exponent, through beta=1. -/
theorem exists_sqrt_log_mass_of_polar_bound {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 2 N, |b n|) ≤ C*Real.sqrt N*(1+Real.log N)^β := by
  let D := 2*Real.pi*‖ell‖*(1+sublogResonatorConstant^β)
  let B : ℕ → ℝ := fun N => D*(1+Real.log N)^β
  have hconst0 : 0 ≤ sublogResonatorConstant := le_trans (by norm_num) one_le_sublogResonatorConstant
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB (N : ℕ) (hN : 1≤N) : 0≤B N := by
    have hl := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
    dsimp [B]
    positivity
  have hmono (M N : ℕ) (hM : 1≤M) (hMN : M≤N) : B M≤B N := by
    have hMr : (1:ℝ)≤M := by exact_mod_cast hM
    have hl := Real.log_le_log (by linarith : (0:ℝ)<M)
      (show (M:ℝ)≤N by exact_mod_cast hMN)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [Real.log_nonneg hMr]) (by linarith) hβ) hD
  have hp (N : ℕ) (hN : 1≤N) (S : Finset ℕ) (hs : S ⊆ Finset.Icc 2 N)
      (hS : WeilMeanSquare.IsPrimitiveSet S) : (∑ n ∈ S,b n^2) ≤ (B N)^2 := by
    let L := 2*Real.pi*‖ell‖*(1+(Real.log N+sublogResonatorConstant)^β)
    have hL : 0≤L := by
      have hl := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
      dsimp [L]
      positivity
    have hLB : L≤B N := by
      have hh := mul_le_mul_of_nonneg_left (resonator_budget_growth hβ hN)
        (show 0≤2*Real.pi*‖ell‖ by positivity)
      simpa only [L,B,D,mul_assoc] using hh
    have hh := primitive_square_of_toeplitz hN hL
      (log_toeplitz_of_polar_bound hβ hβ1 h N hN) S hs hS
    exact hh.trans (by nlinarith [hB N hN])
  refine ⟨4*D,by positivity,fun N hN => ?_⟩
  have hh := sum_abs_le_four_sqrt_of_primitive hB hmono hp N hN
  simpa only [B,mul_assoc,mul_comm,mul_left_comm] using hh

end RHTower.ExposingRayTransfer
