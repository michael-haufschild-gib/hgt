import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ResonantReturns.PairDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.FirstWait

/-! # Sharp fine-precision return index on a clock with a rational pair -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ResonantReturns
open PrecisionReturns
noncomputable section

/-- Index of the first strictly positive affordable tick. -/
def firstIndex {n : ℕ} (H : selfAdjoint (Register n)) (τ : ℝ) (s : ℕ) (ε : ℝ) : ℕ :=
  sInf {q : ℕ | 1≤q ∧ HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val ((q:ℝ)*τ))}

/-- A continuous lower exponent and a discrete Dirichlet deadline of the
same degree determine the exact physical first-index exponent. -/
theorem exponent_of_deadline {n d : ℕ} (H : selfAdjoint (Register n)) {τ : ℝ} (hτ : 0<τ) (s : ℕ)
    (hl : Tendsto (fun ε => log (firstVisit H τ s ε-τ)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 (d:ℝ)))
    {C : ℝ} (hC : 0<C)
    (hu : ∀ ε ∈ Ioo (0:ℝ) 1, ∃ q : ℕ, 1≤q ∧ (q:ℝ)≤C*(1/ε)^d ∧
      HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val ((q:ℝ)*τ))) :
    Tendsto (fun ε => log (firstIndex H τ s ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 (d:ℝ)) := by
  have hlo := hl.sub (tendsto_const_div_log_one_div (log (1+τ)))
  have hhi := (tendsto_const_div_log_one_div (log C)).add (tendsto_const_nhds (x:=(d:ℝ)))
  rw [sub_zero] at hlo
  rw [zero_add] at hhi
  have hboth : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      (log (firstVisit H τ s ε-τ)-log (1+τ))/log (1/ε) ≤ log (firstIndex H τ s ε)/log (1/ε) ∧
      log (firstIndex H τ s ε)/log (1/ε) ≤ log C/log (1/ε)+(d:ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    obtain ⟨q,hq,hb,hfit⟩ := hu ε hε
    let m := firstIndex H τ s ε
    let A := {j : ℕ | 1≤j ∧ HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val ((j:ℝ)*τ))}
    have hqA : q∈A := ⟨hq,hfit⟩
    have hm : m∈A := Nat.sInf_mem ⟨q,hqA⟩
    have hm1 : 1≤(m:ℝ) := by exact_mod_cast hm.1
    have hm0 : 0<(m:ℝ) := zero_lt_one.trans_le hm1
    have hlog := log_pos ((one_lt_div hε.1).mpr hε.2)
    have hv := firstVisit_isLeast H τ s hε.1
    have hvle := hv.2 (show (m:ℝ)*τ ∈ PrecisionReturns.visitSet H τ s ε from
      ⟨le_mul_of_one_le_left hτ.le hm1,hm.2⟩)
    have hlow : log (firstVisit H τ s ε-τ) ≤ log ((1+τ)*(m:ℝ)) := by
      rcases (sub_nonneg.mpr hv.1.1).eq_or_lt with h0|hp
      · rw [←h0,log_zero]
        exact log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith only [hτ]) hm1)
      · exact log_le_log hp (by nlinarith only [hvle,hτ,hm0])
    rw [log_mul (by positivity) hm0.ne'] at hlow
    refine ⟨div_le_div_of_nonneg_right (sub_le_iff_le_add'.mpr hlow) hlog.le,?_⟩
    have hmle : (m:ℝ)≤C*(1/ε)^d := (Nat.cast_le.mpr (Nat.sInf_le hqA)).trans hb
    have hlogle := log_le_log hm0 hmle
    rw [log_mul hC.ne' (pow_ne_zero _ (one_div_pos.mpr hε.1).ne'),log_pow] at hlogle
    calc
      _ ≤ (log C + (d:ℝ)*log (1/ε))/log (1/ε) := div_le_div_of_nonneg_right hlogle hlog.le
      _ = _ := by rw [add_div,mul_div_cancel_right₀ _ hlog.ne']
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · exact hboth.mono fun ε hε => by simpa only [sub_div] using hε.1
  · exact hboth.mono fun _ hε => hε.2

/-- A scalar fit at error M/Q by tick L Q^d, combined with the
continuous first-visit lower exponent d, fixes the disconnected
first-index exponent at d. -/
theorem exponent_of_scalar_deadline {n d : ℕ} (H : selfAdjoint (Register n)) {τ : ℝ} (hτ : 0 < τ) (s : ℕ)
    (hl : Tendsto (fun ε => log (firstVisit H τ s ε-τ)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 (d:ℝ)))
    {L : ℕ} (hL : 0 < L) {M : ℝ} (hM : 0 < M)
    (hdeadline : ∀ Q : ℕ, 0 < Q → ∃ q : ℕ, 1 ≤ q ∧ q ≤ L*Q^d ∧
      HasProjectiveCircuitApproximation n (M/Q) 0 (unitaryEvolution H.val ((q:ℝ)*τ))) :
    Tendsto (fun ε => log (firstIndex H τ s ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 (d:ℝ)) := by
  let C := (L:ℝ)*(M+1)^d
  apply exponent_of_deadline H hτ s hl (C:=C) (by dsimp only [C]; positivity)
  intro ε hε
  let Q := ⌈M/ε⌉₊
  have hratio : 0<M/ε := div_pos hM hε.1
  have hQ : 0<Q := Nat.ceil_pos.mpr hratio
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have htol : M/(Q:ℝ)≤ε := by
    apply (div_le_iff₀ hQr).mpr
    rw [mul_comm ε (Q:ℝ)]
    exact (div_le_iff₀ hε.1).mp (Nat.le_ceil (M/ε))
  obtain ⟨q,hq,hbound,c,hc,W,hW,hfit⟩ := hdeadline Q hQ
  refine ⟨q,hq,?_,c,hc,W,hW.trans (Nat.zero_le _),hfit.trans htol⟩
  have hbound' : (q:ℝ)≤(L:ℝ)*(Q:ℝ)^d := by exact_mod_cast hbound
  have ht : (Q:ℝ)≤(M+1)/ε := calc
    _ ≤ M/ε+1 := (Nat.ceil_lt_add_one hratio.le).le
    _ ≤ _ := (le_div_iff₀ hε.1).mpr (by rw [add_mul,div_mul_cancel₀ _ hε.1.ne',one_mul]; linarith only [hε.2])
  apply hbound'.trans
  calc
    _ ≤ (L:ℝ)*((M+1)/ε)^d := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQr.le ht d) (Nat.cast_nonneg L)
    _ = _ := by dsimp only [C]; rw [div_eq_mul_one_div,mul_pow,mul_assoc]

/-- At every positive clock admitting a rational pair of eigenphases,
the first tick affordable by a disconnected circuit has precision exponent
D−2. All such clocks and budgets are allowed on the same frozen chain. -/
theorem gaussian_rational_pair_first_index :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues
      ∀ τ > (0:ℝ), ∀ a b : Fin N → Bool, a≠b → ∀ L : ℕ, 0<L → ∀ z : ℤ,
        (L:ℝ)*τ*(E b-E a)/(2*π)=z → ∀ s : ℕ, s+1<N →
        Tendsto (fun ε => log (firstIndex H τ s ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  filter_upwards [DisconnectedReturns.gaussian_disconnected_first_wait] with ω hω k
  intro N H E τ hτ a b hab L hL z hz s hs
  exact exponent_of_scalar_deadline H hτ s (hω k τ hτ s hs) hL (mul_pos two_pos pi_pos)
    (fun _ hQ => rational_pair_deadline H τ a b hab hL z hz hQ)

#print axioms gaussian_rational_pair_first_index
end
end GaloisForLFunctions.HTGeometry.ResonantReturns
