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
