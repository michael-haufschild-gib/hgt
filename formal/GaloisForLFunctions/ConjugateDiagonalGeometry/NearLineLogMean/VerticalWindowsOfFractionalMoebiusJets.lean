import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.FractionalIntegrationOfRandomMoebiusJets
import GaloisForLFunctions.RHTower.SmoothAFEReflectedCofactorTransfer
import GaloisForLFunctions.RHTower.ZetaFiniteMeanSquare
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDyadicDensity

/-!
# Vertical mean squares of fractional Möbius derivatives

The logarithmic prime-phase flow turns the Riesz potential of each
finite jet into a literal Dirichlet polynomial on a vertical line.
Montgomery–Vaughan compares every translated window with the Haar
second moment. At the borderline α=k+1/2 the weight in its error
is μ(n)²/log n, so windows of length N/log N already detect divergence.
-/

noncomputable section
open Finset Filter Topology MeasureTheory ArithmeticFunction
open _root_.RHTower _root_.RHTower.SteinhausModel
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Energy along a single vertical orbit of the prime phases. -/
def moebiusJetWindow (N k : ℕ) (α : ℝ) (ω : Omega) (A U : ℝ) : ℝ :=
  ∫ t in A..(A+U), ‖moebiusJetPotential N k α (steinhausLogPhaseShift ω (-t))‖^2

/-- Haar energy of the same polynomial. -/
def moebiusJetEnergy (N k : ℕ) (α : ℝ) : ℝ :=
  ∫ ω, ‖moebiusJetPotential N k α ω‖^2 ∂steinhausMeasure

private theorem energy_as_sum (N k : ℕ) {α : ℝ} (hα : 0 < α) :
    moebiusJetEnergy N k α = ∑ n ∈ Icc 2 N, moebiusJetAmplitude k α n^2 := by
  rw [moebiusJetEnergy,moebiusJetPotential_second_moment _ _ hα]
  exact sum_congr rfl fun n hn => (moebiusJetAmplitude_sq k α (mem_Icc.mp hn).1).symm

private theorem sum_modes {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℕ → E) :
    (∑ i : Fin N, if 2 ≤ i.val+1 then f (i.val+1) else 0) = ∑ n ∈ Icc 2 N, f n := by
  let g (n : ℕ) := if 2 ≤ n then f n else 0
  have H : (∑ i : Fin N, g (i.val+1)) = ∑ n ∈ Icc 1 N, g n := by
    rw [←Sieve.image_succ_univ N,sum_image (Sieve.succ_injOn N)]
  have he : (Icc 1 N).filter (2 ≤ ·) = Icc 2 N := by
    ext n; simp only [mem_filter,mem_Icc]; omega
  simpa only [g,←sum_filter,he] using H

private def orbitCoeff (N k : ℕ) (α : ℝ) (ω : Omega) (i : Fin N) : ℂ :=
  if 2 ≤ i.val+1 then (moebiusJetAmplitude k α (i.val+1):ℂ)*X (i.val+1) ω else 0

private theorem orbit_polynomial (N k : ℕ) {α : ℝ} (hα : 0 < α) (ω : Omega) (t : ℝ) :
    moebiusJetPotential N k α (steinhausLogPhaseShift ω (-t)) =
      Sieve.dirPoly N (orbitCoeff N k α ω) (-t) := by
  rw [moebiusJetPotential_fourier _ _ hα,Sieve.dirPoly]
  let f (n : ℕ) := (moebiusJetAmplitude k α n:ℂ)*X n ω*
    Complex.exp (((-t*Real.log n:ℝ):ℂ)*Complex.I)
  have hleft : (∑ n ∈ Icc 2 N, (moebiusJetAmplitude k α n:ℂ)*X n (steinhausLogPhaseShift ω (-t))) =
      ∑ n ∈ Icc 2 N, f n := by
    apply sum_congr rfl
    intro n hn
    have hn₀ : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    rw [X_steinhausLogPhaseShift _ _ hn₀,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn₀),
      ←Complex.natCast_log]
    dsimp only [f]
    rw [show (Real.log n:ℂ)*((↑(-t):ℂ)*Complex.I) =
      ((-t*Real.log n:ℝ):ℂ)*Complex.I by push_cast; ring]
    ring
  rw [hleft,←sum_modes N f]
  exact sum_congr rfl fun i _ => by
    by_cases hi : 2 ≤ i.val+1
    · simp only [f,orbitCoeff,if_pos hi,Nat.cast_add_one]
    · simp only [orbitCoeff,if_neg hi,zero_mul]

private theorem orbit_norm (N k : ℕ) (α : ℝ) (ω : Omega) (i : Fin N) :
    ‖orbitCoeff N k α ω i‖^2 = if 2 ≤ i.val+1 then moebiusJetAmplitude k α (i.val+1)^2 else 0 := by
  by_cases hi : 2 ≤ i.val+1 <;>
    simp [orbitCoeff,hi,norm_mul,norm_X,Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Every phase and every observation window have the same diagonal.
The error keeps the individual frequency indices as weights. -/
theorem fractional_moebius_window_error (N k : ℕ) {α : ℝ} (hα : 0 < α) (ω : Omega) (A U : ℝ) :
    |moebiusJetWindow N k α ω A U-U*moebiusJetEnergy N k α| ≤
      208*∑ n ∈ Icc 2 N, (n:ℝ)*moebiusJetAmplitude k α n^2 := by
  have H := Sieve.dirichlet_meanValue_sharp_window_neg N (orbitCoeff N k α ω) A (A+U)
  simp_rw [orbit_norm] at H
  have he : (∑ i : Fin N, ((i:ℝ)+1)*(if 2 ≤ i.val+1 then moebiusJetAmplitude k α (i.val+1)^2 else 0)) =
      ∑ n ∈ Icc 2 N, (n:ℝ)*moebiusJetAmplitude k α n^2 := by
    simpa only [Nat.cast_add_one,mul_ite,mul_zero] using
      (sum_modes N fun n => (n:ℝ)*moebiusJetAmplitude k α n^2)
  rw [he,sum_modes N (fun n => moebiusJetAmplitude k α n^2),add_sub_cancel_left] at H
  simpa only [moebiusJetWindow,orbit_polynomial _ _ hα,energy_as_sum _ _ hα] using H

private theorem energy_sandwich (N k : ℕ) {α U : ℝ} (hα : 0 < α) (hU : 0 < U)
    (hN : 416*(N:ℝ) ≤ U) (ω : Omega) (A : ℝ) :
    moebiusJetEnergy N k α/2 ≤ moebiusJetWindow N k α ω A U/U ∧
      moebiusJetWindow N k α ω A U/U ≤ 3*moebiusJetEnergy N k α/2 := by
  have hu := fractional_moebius_window_error N k hα ω A U
  have he : (∑ n ∈ Icc 2 N, (n:ℝ)*moebiusJetAmplitude k α n^2) ≤ (N:ℝ)*moebiusJetEnergy N k α := by
    rw [energy_as_sum _ _ hα,mul_sum]
    exact sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (mem_Icc.mp hn).2) (sq_nonneg _)
  have h₀ : 0 ≤ moebiusJetEnergy N k α := by rw [energy_as_sum _ _ hα]; positivity
  have hc := mul_le_mul_of_nonneg_right hN h₀
  rw [le_div_iff₀ hU,div_le_iff₀ hU]
  constructor <;> linarith only [(abs_le.mp hu).1,(abs_le.mp hu).2,he,hc]

/-- One window per cutoff per arbitrary choice of phase detects the
exact regularity threshold. Both the phase and the origin may change with N. -/
theorem single_window_fractional_threshold (k : ℕ) {α : ℝ} (hα : 0 < α)
    (ω : ℕ → Omega) (A U : ℕ → ℝ) (hU : ∀ N, 0 < U N) (hN : ∀ N : ℕ, 416*(N:ℝ) ≤ U N) :
    (∃ C : ℝ, ∀ N, moebiusJetWindow N k α (ω N) (A N) (U N)/U N ≤ C) ↔ (k:ℝ)+1/2 < α := by
  rw [←uniform_random_jet_second_moment_iff k hα]
  constructor
  · rintro ⟨C,H⟩
    exact ⟨2*C,fun N => by
      change moebiusJetEnergy N k α ≤ _
      linarith only [(energy_sandwich N k hα (hU N) (hN N) (ω N) (A N)).1,H N]⟩
  · rintro ⟨C,H⟩
    refine ⟨3*C/2,fun N => ?_⟩
    have he : moebiusJetEnergy N k α ≤ C := H N
    linarith only [(energy_sandwich N k hα (hU N) (hN N) (ω N) (A N)).2,he]

private theorem borderline_cost (k : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Icc 2 N, (n:ℝ)*moebiusJetAmplitude k (k+1/2) n^2)*Real.log N ≤
      (N:ℝ)*(2+2/Real.log 2) := by
  classical
  let H := Nat.sqrt N
  let c := Real.log N/Real.log 2
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N from hN))
  have hc : 0 ≤ c := div_nonneg hlog.le h₂.le
  have hrow (n : ℕ) (hn : n ∈ Icc 2 N) :
      (n:ℝ)*moebiusJetAmplitude k (k+1/2) n^2*Real.log N ≤
        2+(if n ≤ H then c else 0) := by
    have hn' := (mem_Icc.mp hn).1
    have hr : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn')
    have hm : ((moebius n:ℤ):ℝ)^2 ≤ 1 := by
      rw [←Int.cast_pow,moebius_sq]; split <;> norm_num
    have he : (n:ℝ)*moebiusJetAmplitude k (k+1/2) n^2*Real.log N =
        ((moebius n:ℤ):ℝ)^2*(Real.log N/Real.log n) := by
      rw [moebiusJetAmplitude_sq k _ hn',show 2*((k:ℝ)-(k+1/2)) = -1 by ring,Real.rpow_neg_one]
      field_simp
    rw [he]
    apply (mul_le_mul_of_nonneg_right hm (div_nonneg hlog.le (h₂.le.trans hl))).trans
    rw [one_mul]
    by_cases hs : n ≤ H
    · rw [if_pos hs]
      have hh : Real.log N/Real.log n ≤ c := div_le_div_of_nonneg_left hlog.le h₂ hl
      linarith only [hh]
    · have hsq : N ≤ n^2 := (Nat.lt_succ_sqrt' N).le.trans
        (Nat.pow_le_pow_left (show Nat.sqrt N+1 ≤ n by omega) _)
      have hh := Real.log_le_log hNr (show (N:ℝ) ≤ (n:ℝ)^2 by exact_mod_cast hsq)
      rw [Real.log_pow] at hh
      rw [if_neg hs,add_zero,div_le_iff₀ (h₂.trans_le hl)]
      exact_mod_cast hh
  let S := Icc 2 N
  have hcard : S.card ≤ N := by simp only [S,Nat.card_Icc]; omega
  have hsmall : (S.filter (· ≤ H)).card ≤ H := by
    have hh : S.filter (· ≤ H) ⊆ Icc 1 H := by
      intro n hn
      obtain ⟨hn',hle⟩ := mem_filter.mp hn
      exact mem_Icc.mpr ⟨le_trans (Nat.le_succ 1) (mem_Icc.mp hn').1,hle⟩
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hh
  have hsum := sum_le_sum (s:=S) hrow
  rw [sum_add_distrib,←sum_filter,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul] at hsum
  have hsqrt := Sieve.natSqrt_le_sqrt N
  have hx := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hNr)
  rw [Real.log_sqrt hNr.le] at hx
  have hc' : (H:ℝ)*c ≤ 2*(N:ℝ)/Real.log 2 := by
    rw [show (H:ℝ)*c=((H:ℝ)*Real.log N)/Real.log 2 by dsimp only [c]; ring]
    apply div_le_div_of_nonneg_right _ h₂.le
    calc _ ≤ Real.sqrt N * (2*Real.sqrt N) := mul_le_mul hsqrt (by linarith only [hx])
               hlog.le (Real.sqrt_nonneg _)
         _ = _ := by nlinarith only [Real.sq_sqrt hNr.le]
  rw [sum_mul]
  have hlarge := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard : (S.card:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 2)
  have hshort := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hsmall : ((S.filter (· ≤ H)).card:ℝ) ≤ H) hc
  exact hsum.trans ((add_le_add hlarge (hshort.trans hc')).trans_eq (by ring))

/-- At α=k+1/2, a window of length N/log N recovers the Haar energy
with an absolute error independent of the origin, cutoff and order. -/
theorem borderline_log_window_error (k : ℕ) {N : ℕ} (hN : 2 ≤ N) (ω : Omega) (A : ℝ) :
    let U := (N:ℝ)/Real.log N
    |moebiusJetWindow N k (k+1/2) ω A U/U-moebiusJetEnergy N k (k+1/2)| ≤
      208*(2+2/Real.log 2) := by
  let U := (N:ℝ)/Real.log N
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N from hN))
  have hu : 0 < U := div_pos hn hl
  let D := moebiusJetEnergy N k (k+1/2)
  let I := moebiusJetWindow N k (k+1/2) ω A U
  have h := fractional_moebius_window_error N k (by positivity : (0:ℝ) < k+1/2) ω A U
  change |I-U*D| ≤ _ at h
  change |I/U-D| ≤ _
  rw [show I/U-D=(I-U*D)/U by field_simp,abs_div,abs_of_pos hu,div_le_iff₀ hu]
  refine h.trans ?_
  have H := (le_div_iff₀ hl).mpr (borderline_cost k hN)
  apply (mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ) ≤ 208)).trans_eq
  dsimp only [U]
  ring

/-- The borderline energy diverges along every moving sequence of
phases and starting heights, even on the shorter N/log N windows. -/
theorem borderline_fractional_windows_diverge (k : ℕ) (ω : ℕ → Omega) (A : ℕ → ℝ) :
    Tendsto (fun N : ℕ => let U := (N:ℝ)/Real.log N
      moebiusJetWindow N k (k+1/2) (ω N) (A N) U/U) atTop atTop := by
  let α := (k:ℝ)+1/2
  have hα : 0 < α := by dsimp only [α]; positivity
  have hbd : ¬ ∃ C : ℝ, ∀ N, moebiusJetEnergy N k α ≤ C :=
    fun h => (lt_irrefl α) ((uniform_random_jet_second_moment_iff k hα).mp h)
  have hmono : Monotone (fun N => moebiusJetEnergy N k α) := by
    intro M N hMN
    simp only [energy_as_sum _ _ hα]
    exact sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Icc.mpr
      ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hMN⟩) (fun _ _ _ => sq_nonneg _)
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨M,hM⟩ : ∃ M, b+208*(2+2/Real.log 2) < moebiusJetEnergy M k α := by
    by_contra! H
    exact hbd ⟨_,H⟩
  filter_upwards [eventually_ge_atTop (max 2 M)] with N hN
  have h := borderline_log_window_error k ((le_max_left 2 M).trans hN) (ω N) (A N)
  have h' := hmono ((le_max_right 2 M).trans hN)
  dsimp only [α] at hM h'
  let U := (N:ℝ)/Real.log N
  have hlo : -(208*(2+2/Real.log 2)) ≤ moebiusJetWindow N k (k+1/2) (ω N) (A N) U/U - moebiusJetEnergy N k (k+1/2) := (abs_le.mp h).1
  change b ≤ moebiusJetWindow N k (k+1/2) (ω N) (A N) U/U
  linarith only [hlo,hM,h']


end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
