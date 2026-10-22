import GaloisForLFunctions.RHTower.SymmetricHyperbolaFloorCount
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.BlaschkeLocalizedClockAsymptotic
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.SelbergSymmetryCore
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDyadicDensity
import GaloisForLFunctions.RHTower.Sieve.TwoRangeSchedule

open scoped BigOperators
open Filter Topology Asymptotics

namespace RHTower

open Finset ArithmeticFunction

noncomputable section

/-- Symmetric Dirichlet hyperbola identity with an arbitrary real arithmetic weight. -/
theorem sum_Icc_mul_apply_add_sqrt_prefix_sq
    (f : ArithmeticFunction ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (f * f) n) +
        (∑ n ∈ Finset.Icc 1 (Nat.sqrt N), f n) ^ 2 =
      2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt N),
        f d * ∑ m ∈ Finset.Icc 1 (N / d), f m := by
  set s := Nat.sqrt N with hs
  have hIcc : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := by
    intro M
    ext d
    rw [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hunion : Finset.Ioc 0 s ∪ Finset.Ioc s N = Finset.Ioc 0 N :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le s) hsN
  have hdisj : Disjoint (Finset.Ioc (0 : ℕ) s) (Finset.Ioc s N) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hge : ∀ m ∈ Finset.Ioc 0 s, s ≤ N / m := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Nat.le_div_iff_mul_le (by omega : 0 < m)]
    calc s * m ≤ s * s := Nat.mul_le_mul_left s hm.2
      _ ≤ N := by
        rw [hs]
        exact Nat.sqrt_le N
  have htailSwap :
      ∑ d ∈ Finset.Ioc s N, f d * ∑ m ∈ Finset.Icc 1 (N / d), f m =
        ∑ m ∈ Finset.Ioc 0 s, f m * ∑ d ∈ Finset.Ioc s (N / m), f d := by
    rw [show (∑ d ∈ Finset.Ioc s N,
        f d * ∑ m ∈ Finset.Icc 1 (N / d), f m) =
        ∑ x ∈ (Finset.Ioc s N).sigma (fun d => Finset.Icc 1 (N / d)),
          f x.1 * f x.2 by
      calc
        (∑ d ∈ Finset.Ioc s N,
            f d * ∑ m ∈ Finset.Icc 1 (N / d), f m) =
            ∑ d ∈ Finset.Ioc s N, ∑ m ∈ Finset.Icc 1 (N / d),
              f d * f m := by
                apply Finset.sum_congr rfl
                intro d _hd
                rw [Finset.mul_sum]
        _ = _ := Finset.sum_sigma' _ _ _]
    rw [show (∑ m ∈ Finset.Ioc 0 s,
        f m * ∑ d ∈ Finset.Ioc s (N / m), f d) =
        ∑ y ∈ (Finset.Ioc 0 s).sigma (fun m => Finset.Ioc s (N / m)),
          f y.1 * f y.2 by
      calc
        (∑ m ∈ Finset.Ioc 0 s,
            f m * ∑ d ∈ Finset.Ioc s (N / m), f d) =
            ∑ m ∈ Finset.Ioc 0 s, ∑ d ∈ Finset.Ioc s (N / m),
              f m * f d := by
                apply Finset.sum_congr rfl
                intro m _hm
                rw [Finset.mul_sum]
        _ = _ := Finset.sum_sigma' _ _ _]
    apply Finset.sum_nbij'
      (i := fun x => ⟨x.2, x.1⟩) (j := fun y => ⟨y.2, y.1⟩)
    · rintro ⟨d, m⟩ hx
      rw [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc] at hx
      dsimp only at hx
      obtain ⟨⟨hsd, hdN⟩, hm1, hmNd⟩ := hx
      rw [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Ioc]
      dsimp only
      have hmd : m * d ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmNd
      have hms : m ≤ s := by
        by_contra hms
        have hmul := Nat.mul_le_mul
          (show s + 1 ≤ m by omega) (show s + 1 ≤ d by omega)
        have hN := Nat.lt_succ_sqrt N
        rw [← hs] at hN
        have : s.succ * s.succ = (s + 1) * (s + 1) := rfl
        omega
      refine ⟨⟨by omega, hms⟩, hsd, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega : 0 < m)]
      rw [mul_comm] at hmd
      exact hmd
    · rintro ⟨m, d⟩ hy
      rw [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Ioc] at hy
      dsimp only at hy
      obtain ⟨⟨hm0, hms⟩, hsd, hdNm⟩ := hy
      rw [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc]
      dsimp only
      have hdm : d * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hdNm
      refine ⟨⟨hsd, ?_⟩, by omega, ?_⟩
      · calc d ≤ N / m := hdNm
          _ ≤ N := Nat.div_le_self N m
      · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
        rw [mul_comm] at hdm
        exact hdm
    · rintro ⟨d, m⟩ _
      rfl
    · rintro ⟨m, d⟩ _
      rfl
    · rintro ⟨d, m⟩ _
      ring
  have hinner : ∀ m ∈ Finset.Ioc 0 s,
      ∑ d ∈ Finset.Ioc s (N / m), f d =
        (∑ d ∈ Finset.Ioc 0 (N / m), f d) -
          ∑ d ∈ Finset.Ioc 0 s, f d := by
    intro m hm
    have hmge := hge m hm
    have hu : Finset.Ioc 0 s ∪ Finset.Ioc s (N / m) =
        Finset.Ioc 0 (N / m) :=
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le s) hmge
    have hd : Disjoint (Finset.Ioc (0 : ℕ) s) (Finset.Ioc s (N / m)) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [← hu, Finset.sum_union hd]
    ring
  have htailExpand :
      (∑ m ∈ Finset.Ioc 0 s,
        f m * ∑ d ∈ Finset.Ioc s (N / m), f d) =
      ∑ m ∈ Finset.Ioc 0 s,
        f m * ((∑ d ∈ Finset.Ioc 0 (N / m), f d) -
          ∑ d ∈ Finset.Ioc 0 s, f d) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hinner m hm]
  rw [sum_Icc_mul_apply f f N, hIcc N, hIcc s, ← hunion,
    Finset.sum_union hdisj, htailSwap, htailExpand]
  simp_rw [hIcc]
  rw [show (∑ m ∈ Finset.Ioc 0 s,
      f m * ((∑ d ∈ Finset.Ioc 0 (N / m), f d) -
        ∑ d ∈ Finset.Ioc 0 s, f d)) =
      (∑ m ∈ Finset.Ioc 0 s,
        f m * ∑ d ∈ Finset.Ioc 0 (N / m), f d) -
      (∑ m ∈ Finset.Ioc 0 s, f m) ^ 2 by
    rw [show (∑ m ∈ Finset.Ioc 0 s,
        f m * ((∑ d ∈ Finset.Ioc 0 (N / m), f d) -
          ∑ d ∈ Finset.Ioc 0 s, f d)) =
        ∑ m ∈ Finset.Ioc 0 s,
          (f m * ∑ d ∈ Finset.Ioc 0 (N / m), f d -
            f m * ∑ d ∈ Finset.Ioc 0 s, f d) by
      apply Finset.sum_congr rfl
      intro m _hm
      ring,
      Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring]
  ring

/-- The natural square-root aperture is cofinal. -/
theorem tendsto_natSqrt_atTop_cCMFUSuzukiSecondGradeAsymptotic :
    Filter.Tendsto Nat.sqrt Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro K
  refine ⟨K * K, fun N hN => ?_⟩
  exact Nat.le_sqrt.mpr hN

/-- The square-root lattice overlap has asymptotically full area. -/
theorem tendsto_natSqrt_sq_div_self :
    Filter.Tendsto (fun N : ℕ =>
      (((Nat.sqrt N : ℕ) : ℝ) ^ 2) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  have hsReal : Filter.Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop_cCMFUSuzukiSecondGradeAsymptotic
  have hden : Filter.Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 hsReal
  have hinv : Filter.Tendsto (fun N : ℕ =>
      1 / (((Nat.sqrt N : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hden
  have hratio : Filter.Tendsto (fun N : ℕ =>
      ((Nat.sqrt N : ℕ) : ℝ) / (((Nat.sqrt N : ℕ) : ℝ) + 1))
      Filter.atTop (nhds 1) := by
    have hsub : Filter.Tendsto (fun N : ℕ =>
        1 - 1 / (((Nat.sqrt N : ℕ) : ℝ) + 1))
        Filter.atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hinv
    convert hsub using 1
    · funext N
      have hpos : (0 : ℝ) < ((Nat.sqrt N : ℕ) : ℝ) + 1 := by positivity
      field_simp
      ring
    · ring
  have hlower := hratio.pow 2
  have hlowerEventually : ∀ᶠ N : ℕ in Filter.atTop,
      (((Nat.sqrt N : ℕ) : ℝ) /
          (((Nat.sqrt N : ℕ) : ℝ) + 1)) ^ 2 ≤
        (((Nat.sqrt N : ℕ) : ℝ) ^ 2) / (N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hspos : (0 : ℝ) < ((Nat.sqrt N : ℕ) : ℝ) + 1 := by positivity
    have hsq : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
    have hlt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by
      simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hspos) hNpos).2
    have hltNat : N ≤ (Nat.sqrt N + 1) ^ 2 := by
      simpa [pow_two] using hlt.le
    have hltReal : (N : ℝ) ≤ (((Nat.sqrt N + 1 : ℕ) : ℝ)) ^ 2 := by
      exact_mod_cast hltNat
    push_cast at hltReal
    exact mul_le_mul_of_nonneg_left hltReal (sq_nonneg _)
  have hupperEventually : ∀ᶠ N : ℕ in Filter.atTop,
      (((Nat.sqrt N : ℕ) : ℝ) ^ 2) / (N : ℝ) ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    rw [div_le_one hNpos]
    have hsqNat : (Nat.sqrt N) ^ 2 ≤ N := by
      simpa [pow_two] using Nat.sqrt_le N
    exact_mod_cast hsqNat
  have hlower' : Filter.Tendsto (fun N : ℕ =>
      (((Nat.sqrt N : ℕ) : ℝ) /
          (((Nat.sqrt N : ℕ) : ℝ) + 1)) ^ 2)
      Filter.atTop (nhds 1) := by simpa using hlower
  have hresult := Filter.Tendsto.squeeze' hlower'
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 1)) hlowerEventually hupperEventually
  simpa using hresult

/-- The symmetric hyperbola overlap carries the full prime mass asymptotically. -/
theorem tendsto_chebyshevPsi_natSqrt_sq_div_self :
    Filter.Tendsto (fun N : ℕ =>
      chebyshevPsi (Nat.sqrt N) ^ 2 / (N : ℝ))
      Filter.atTop (nhds 1) := by
  have hpsi : Filter.Tendsto (fun N : ℕ =>
      chebyshevPsi (Nat.sqrt N) / ((Nat.sqrt N : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
    have h := tendsto_psi_natCast_div.comp tendsto_natSqrt_atTop_cCMFUSuzukiSecondGradeAsymptotic
    change Filter.Tendsto (fun N : ℕ =>
      Chebyshev.psi ((Nat.sqrt N : ℕ) : ℝ) /
        ((Nat.sqrt N : ℕ) : ℝ)) Filter.atTop (nhds 1) at h
    exact h.congr fun N => by rw [chebyshevPsi_eq_psi]
  have hproduct := (hpsi.pow 2).mul tendsto_natSqrt_sq_div_self
  have heq : (fun N : ℕ =>
      (chebyshevPsi (Nat.sqrt N) / ((Nat.sqrt N : ℕ) : ℝ)) ^ 2 *
        ((((Nat.sqrt N : ℕ) : ℝ) ^ 2) / (N : ℝ))) =ᶠ[Filter.atTop]
      (fun N : ℕ => chebyshevPsi (Nat.sqrt N) ^ 2 / (N : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hs : Nat.sqrt N ≠ 0 :=
      ne_of_gt (Nat.sqrt_pos.2 (by omega : 0 < N))
    field_simp
  simpa using hproduct.congr' heq

/-- The natural square-root floor preserves the logarithmic critical clock. -/
theorem tendsto_two_log_natSqrt_sub_log :
    Filter.Tendsto (fun N : ℕ =>
      2 * Real.log (Nat.sqrt N : ℕ) - Real.log (N : ℝ))
      Filter.atTop (nhds 0) := by
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp
    tendsto_natSqrt_sq_div_self
  have hlogZero : Filter.Tendsto (fun N : ℕ =>
      Real.log ((((Nat.sqrt N : ℕ) : ℝ) ^ 2) / (N : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using hlog
  apply hlogZero.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hs0 : ((Nat.sqrt N : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.sqrt_pos.2 (by omega : 0 < N))
  rw [Real.log_div (pow_ne_zero 2 hs0) hN0, Real.log_pow]
  norm_num

/-- Symmetric half of the von Mangoldt self-convolution hyperbola. -/
def vonMangoldtSelfConvolutionHyperbolaHalf (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (Nat.sqrt N),
    vonMangoldt d * chebyshevPsi (N / d)

/-- Harmonic von Mangoldt mass on the symmetric hyperbola aperture. -/
def vonMangoldtHarmonicSqrtPrefix (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), vonMangoldt d / d

/-- Uniform PNT control on the symmetric hyperbola: after division by `N`, its prime end differs
from the harmonic prime mass only by the PNT saving at `sqrt N` and the exact floor boundary. -/
theorem abs_vonMangoldtSelfConvolutionHyperbolaHalf_div_sub_harmonic_le
    {C c X : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, X ≤ x →
      |Chebyshev.psi x - x| ≤
        C * (x * Real.exp (-c * Real.sqrt (Real.log x))))
    {N : ℕ} (hN : 1 ≤ N) (hX : X ≤ (Nat.sqrt N : ℕ)) :
    |vonMangoldtSelfConvolutionHyperbolaHalf N / (N : ℝ) -
        vonMangoldtHarmonicSqrtPrefix N| ≤
      C * (Real.log (Nat.sqrt N : ℕ) + 7) *
          Real.exp (-c * Real.sqrt (Real.log (Nat.sqrt N : ℕ))) +
        chebyshevPsi (Nat.sqrt N) / (N : ℝ) := by
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.sqrt_pos.2 (by omega : 0 < N)
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogS : 0 ≤ Real.log (s : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hs)
  have hHnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 s, vonMangoldt d / d :=
    Finset.sum_nonneg fun d _hd =>
      div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg d)
  have hHupper : (∑ d ∈ Finset.Icc 1 s, vonMangoldt d / d) ≤
      Real.log (s : ℝ) + 7 := by
    have hm := abs_le.mp (Mertens.mertens_first s hs)
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
      linarith
    linarith
  have hterm : ∀ d ∈ Finset.Icc 1 s,
      |vonMangoldt d * chebyshevPsi (N / d) / (N : ℝ) -
          vonMangoldt d / (d : ℝ)| ≤
        C * Real.exp (-c * Real.sqrt (Real.log (s : ℝ))) *
            (vonMangoldt d / (d : ℝ)) +
          vonMangoldt d / (N : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hds : d ≤ s := (Finset.mem_Icc.mp hd).2
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hyNat : s ≤ N / d := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
      calc s * d ≤ s * s := Nat.mul_le_mul_left s hds
        _ ≤ N := by
          dsimp only [s]
          exact Nat.sqrt_le N
    have hypos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < s) hyNat
    have hXy : X ≤ ((N / d : ℕ) : ℝ) := by
      exact hX.trans (by exact_mod_cast hyNat)
    have hlogMono : Real.log (s : ℝ) ≤ Real.log ((N / d : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hyNat)
    have hsqrtMono : Real.sqrt (Real.log (s : ℝ)) ≤
        Real.sqrt (Real.log ((N / d : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt hlogMono
    have hexpMono :
        Real.exp (-c * Real.sqrt (Real.log ((N / d : ℕ) : ℝ))) ≤
          Real.exp (-c * Real.sqrt (Real.log (s : ℝ))) := by
      rw [Real.exp_le_exp]
      nlinarith
    have hfloorLe : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    have hfloorAbs :
        |((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hfloorLe)]
      have hfloorLt := Mertens.cast_div_lt N d (by omega : 0 < d)
      linarith
    have hpnt :
        |chebyshevPsi (N / d) - ((N / d : ℕ) : ℝ)| ≤
          C * ((N : ℝ) / (d : ℝ)) *
            Real.exp (-c * Real.sqrt (Real.log (s : ℝ))) := by
      rw [chebyshevPsi_eq_psi]
      calc
        |Chebyshev.psi ((N / d : ℕ) : ℝ) - ((N / d : ℕ) : ℝ)|
            ≤ C * (((N / d : ℕ) : ℝ) *
                Real.exp (-c * Real.sqrt
                  (Real.log ((N / d : ℕ) : ℝ)))) := hbound _ hXy
        _ ≤ C * (((N : ℝ) / (d : ℝ)) *
              Real.exp (-c * Real.sqrt
                (Real.log ((N / d : ℕ) : ℝ)))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hfloorLe (Real.exp_nonneg _)) hC
        _ ≤ C * (((N : ℝ) / (d : ℝ)) *
              Real.exp (-c * Real.sqrt (Real.log (s : ℝ)))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexpMono
                (div_nonneg (Nat.cast_nonneg N) hdpos.le)) hC
        _ = C * ((N : ℝ) / (d : ℝ)) *
              Real.exp (-c * Real.sqrt (Real.log (s : ℝ))) := by ring
    have hpsiFloor :
        |chebyshevPsi (N / d) - (N : ℝ) / (d : ℝ)| ≤
          C * ((N : ℝ) / (d : ℝ)) *
              Real.exp (-c * Real.sqrt (Real.log (s : ℝ))) + 1 :=
      (abs_sub_le _ _ _).trans (add_le_add hpnt hfloorAbs)
    have hΛ : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    rw [show vonMangoldt d * chebyshevPsi (N / d) / (N : ℝ) -
        vonMangoldt d / (d : ℝ) =
        (vonMangoldt d / (N : ℝ)) *
          (chebyshevPsi (N / d) - (N : ℝ) / (d : ℝ)) by
      field_simp,
      abs_mul, abs_of_nonneg (div_nonneg hΛ hNpos.le)]
    calc
      vonMangoldt d / (N : ℝ) *
          |chebyshevPsi (N / d) - (N : ℝ) / (d : ℝ)|
          ≤ vonMangoldt d / (N : ℝ) *
              (C * ((N : ℝ) / (d : ℝ)) *
                Real.exp (-c * Real.sqrt (Real.log (s : ℝ))) + 1) :=
            mul_le_mul_of_nonneg_left hpsiFloor
              (div_nonneg hΛ hNpos.le)
      _ = C * Real.exp (-c * Real.sqrt (Real.log (s : ℝ))) *
              (vonMangoldt d / (d : ℝ)) +
            vonMangoldt d / (N : ℝ) := by field_simp
  rw [vonMangoldtSelfConvolutionHyperbolaHalf,
    vonMangoldtHarmonicSqrtPrefix]
  dsimp only [s] at hterm hHnonneg hHupper ⊢
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Icc 1 (Nat.sqrt N),
        (vonMangoldt d * chebyshevPsi (N / d) / (N : ℝ) -
          vonMangoldt d / (d : ℝ))|
        ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N),
            |vonMangoldt d * chebyshevPsi (N / d) / (N : ℝ) -
              vonMangoldt d / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N),
          (C * Real.exp (-c * Real.sqrt (Real.log (Nat.sqrt N : ℕ))) *
              (vonMangoldt d / (d : ℝ)) +
            vonMangoldt d / (N : ℝ)) :=
      Finset.sum_le_sum fun d hd => hterm d hd
    _ = C * Real.exp (-c * Real.sqrt (Real.log (Nat.sqrt N : ℕ))) *
            (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), vonMangoldt d / (d : ℝ)) +
          chebyshevPsi (Nat.sqrt N) / (N : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      congr 1
    _ ≤ C * (Real.log (Nat.sqrt N : ℕ) + 7) *
            Real.exp (-c * Real.sqrt (Real.log (Nat.sqrt N : ℕ))) +
          chebyshevPsi (Nat.sqrt N) / (N : ℝ) := by
      have hfactor : 0 ≤
          C * Real.exp (-c * Real.sqrt (Real.log (Nat.sqrt N : ℕ))) := by
        positivity
      have := mul_le_mul_of_nonneg_left hHupper hfactor
      nlinarith

/-- A logarithmic factor remains negligible against the PNT square-root-log saving. -/
theorem tendsto_log_add_seven_mul_exp_neg_sqrt_log
    {c C : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun x : ℝ =>
      C * (Real.log x + 7) *
        Real.exp (-c * Real.sqrt (Real.log x)))
      Filter.atTop (nhds 0) := by
  have h1 := RHTower.Sieve.tendsto_logRpow_mul_expSaving
    (d := (1 : ℝ) / 2) (s := c) (by norm_num) hc (1 : ℝ)
  have h0 := RHTower.Sieve.tendsto_logRpow_mul_expSaving
    (d := (1 : ℝ) / 2) (s := c) (by norm_num) hc (0 : ℝ)
  have hsum := h1.add (h0.const_mul 7)
  have hscaled := hsum.const_mul C
  simpa only [add_zero, mul_zero] using hscaled.congr' (by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    rw [← Real.sqrt_eq_rpow, Real.rpow_one,
      Real.rpow_zero (Real.log x)]
    ring)

/-- The natural square-root floor divided by its ambient aperture vanishes. -/
theorem tendsto_natSqrt_div_self_zero :
    Filter.Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ tendsto_sqrt_natCast_div_natCast_atTop_zero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  exact div_le_div_of_nonneg_right
    (RHTower.Sieve.natSqrt_le_sqrt N) hN0

/-- The overlap prime boundary divided by the ambient aperture vanishes. -/
theorem tendsto_chebyshevPsi_natSqrt_div_self_zero :
    Filter.Tendsto (fun N : ℕ =>
      chebyshevPsi (Nat.sqrt N) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  have hpsi : Filter.Tendsto (fun N : ℕ =>
      chebyshevPsi (Nat.sqrt N) / ((Nat.sqrt N : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
    have h := tendsto_psi_natCast_div.comp tendsto_natSqrt_atTop_cCMFUSuzukiSecondGradeAsymptotic
    change Filter.Tendsto (fun N : ℕ =>
      Chebyshev.psi ((Nat.sqrt N : ℕ) : ℝ) /
        ((Nat.sqrt N : ℕ) : ℝ)) Filter.atTop (nhds 1) at h
    exact h.congr fun N => by rw [chebyshevPsi_eq_psi]
  have hproduct := hpsi.mul tendsto_natSqrt_div_self_zero
  have heq : (fun N : ℕ =>
      chebyshevPsi (Nat.sqrt N) / ((Nat.sqrt N : ℕ) : ℝ) *
        (((Nat.sqrt N : ℕ) : ℝ) / (N : ℝ))) =ᶠ[Filter.atTop]
      (fun N : ℕ => chebyshevPsi (Nat.sqrt N) / (N : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hs : Nat.sqrt N ≠ 0 :=
      ne_of_gt (Nat.sqrt_pos.2 (by omega : 0 < N))
    field_simp
  simpa using hproduct.congr' heq

/-- The coupled symmetric hyperbola prime end lands on its harmonic Mertens mass. -/
theorem tendsto_vonMangoldtSelfConvolutionHyperbolaHalf_div_sub_harmonic :
    Filter.Tendsto (fun N : ℕ =>
      vonMangoldtSelfConvolutionHyperbolaHalf N / (N : ℝ) -
        vonMangoldtHarmonicSqrtPrefix N)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, c, hc, hC, hboundEventually⟩ := exists_psi_error_eventually
  obtain ⟨X, hbound⟩ := Filter.eventually_atTop.1 hboundEventually
  have hsReal : Filter.Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop_cCMFUSuzukiSecondGradeAsymptotic
  have hupper : Filter.Tendsto (fun N : ℕ =>
      C * (Real.log (Nat.sqrt N : ℕ) + 7) *
          Real.exp (-c * Real.sqrt (Real.log (Nat.sqrt N : ℕ))) +
        chebyshevPsi (Nat.sqrt N) / (N : ℝ))
      Filter.atTop (nhds 0) := by
    have hdecay :=
      (tendsto_log_add_seven_mul_exp_neg_sqrt_log (C := C) hc).comp hsReal
    have hadd := hdecay.add tendsto_chebyshevPsi_natSqrt_div_self_zero
    simpa [Function.comp_def] using hadd
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N => norm_nonneg _)
    ?_ hupper
  filter_upwards [Filter.eventually_ge_atTop 1,
    hsReal.eventually_ge_atTop X] with N hN hXN
  simpa only [Real.norm_eq_abs] using
    abs_vonMangoldtSelfConvolutionHyperbolaHalf_div_sub_harmonic_le
      hC hc hbound hN hXN

/-- Mertens' exact constant survives restriction to the cofinal square-root aperture. -/
theorem tendsto_vonMangoldtHarmonicSqrtPrefix_sub_log :
    Filter.Tendsto (fun N : ℕ =>
      vonMangoldtHarmonicSqrtPrefix N - Real.log (Nat.sqrt N : ℕ))
      Filter.atTop (nhds (-Real.eulerMascheroniConstant)) := by
  have h := tendsto_sum_vonMangoldt_div_sub_log.comp tendsto_natSqrt_atTop_cCMFUSuzukiSecondGradeAsymptotic
  change Filter.Tendsto (fun N : ℕ =>
    (∑ n ∈ Finset.Icc 1 (Nat.sqrt N),
      vonMangoldt n / (n : ℝ)) - Real.log ((Nat.sqrt N : ℕ) : ℝ))
    Filter.atTop (nhds (-Real.eulerMascheroniConstant)) at h
  simpa only [vonMangoldtHarmonicSqrtPrefix] using h

/-- Exact weighted symmetric hyperbola law for the von Mangoldt self-convolution. -/
theorem sum_vonMangoldt_selfConv_add_sqrtPsi_sq (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (vonMangoldt * vonMangoldt) n) +
        chebyshevPsi (Nat.sqrt N) ^ 2 =
      2 * vonMangoldtSelfConvolutionHyperbolaHalf N := by
  simpa only [vonMangoldtSelfConvolutionHyperbolaHalf, chebyshevPsi] using
    sum_Icc_mul_apply_add_sqrt_prefix_sq vonMangoldt N

/-- **Constant-faithful second-grade prime asymptotic.**  The full von Mangoldt
self-convolution has the precise summatory expansion
`N * (log N - 1 - 2 * gamma) + o(N)`.  Both Mertens constants and the symmetric
hyperbola overlap are retained, matching the literal Suzuki polar second variation. -/
theorem tendsto_vonMangoldt_selfConv_summatory_sub_polar_div :
    Filter.Tendsto (fun N : ℕ =>
      ((∑ n ∈ Finset.Icc 1 N, (vonMangoldt * vonMangoldt) n) -
        (N : ℝ) * (Real.log (N : ℝ) - 1 -
          2 * Real.eulerMascheroniConstant)) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  have hhyper :=
    tendsto_vonMangoldtSelfConvolutionHyperbolaHalf_div_sub_harmonic.const_mul 2
  have hmertens :=
    (tendsto_vonMangoldtHarmonicSqrtPrefix_sub_log.add_const
      Real.eulerMascheroniConstant).const_mul 2
  have hlog := tendsto_two_log_natSqrt_sub_log
  have hoverlap : Filter.Tendsto (fun N : ℕ =>
      1 - chebyshevPsi (Nat.sqrt N) ^ 2 / (N : ℝ))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).sub
        tendsto_chebyshevPsi_natSqrt_sq_div_self
    simpa using h
  have hsum := ((hhyper.add hmertens).add hlog).add hoverlap
  have hsumZero : Filter.Tendsto (fun N : ℕ =>
      2 * (vonMangoldtSelfConvolutionHyperbolaHalf N / (N : ℝ) -
          vonMangoldtHarmonicSqrtPrefix N) +
        2 * (vonMangoldtHarmonicSqrtPrefix N -
          Real.log (Nat.sqrt N : ℕ) + Real.eulerMascheroniConstant) +
        (2 * Real.log (Nat.sqrt N : ℕ) - Real.log (N : ℝ)) +
        (1 - chebyshevPsi (Nat.sqrt N) ^ 2 / (N : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hsum
  apply hsumZero.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hid := sum_vonMangoldt_selfConv_add_sqrtPsi_sq N
  field_simp
  nlinarith

/-- Exact second-grade arithmetic-minus-polar prefix discrepancy. -/
def selbergSecondGradePrefixDiscrepancy (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, (vonMangoldt * vonMangoldt) n) -
    (N : ℝ) * (Real.log (N : ℝ) - 1 -
      2 * Real.eulerMascheroniConstant)

theorem tendsto_selbergSecondGradePrefixDiscrepancy_div :
    Tendsto (fun N : ℕ =>
      selbergSecondGradePrefixDiscrepancy N / (N : ℝ))
      atTop (nhds 0) := by
  simpa only [selbergSecondGradePrefixDiscrepancy] using
    tendsto_vonMangoldt_selfConv_summatory_sub_polar_div

/-- Positive square-root Abel mesh weight attached to prefix `k + 1`. -/
def selbergSecondGradeSqrtMeshWeight (k : ℕ) : ℝ :=
  (k + 1 : ℕ) *
    (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))

/-- Total mass of the square-root Abel mesh. -/
def selbergSecondGradeSqrtMeshScale (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, selbergSecondGradeSqrtMeshWeight k

theorem selbergSecondGradeSqrtMeshWeight_nonneg (k : ℕ) :
    0 ≤ selbergSecondGradeSqrtMeshWeight k := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))))

theorem one_third_le_selbergSecondGradeSqrtMeshWeight (k : ℕ) :
    (1 / 3 : ℝ) ≤ selbergSecondGradeSqrtMeshWeight k := by
  let n : ℕ := k + 1
  have hn : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrtn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hn))
  have hsqrtsucc : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    exact Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hdenpos : 0 < Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ) := by
    positivity
  have hden : Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ) ≤ 3 * n := by
    calc
      Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)
          ≤ ((n : ℝ) + 1) + (n : ℝ) := add_le_add hsqrtsucc hsqrtn
      _ ≤ 3 * n := by
        have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
  have hgap : Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ) =
      1 / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) := by
    rw [eq_div_iff hdenpos.ne']
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1),
      Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
  rw [selbergSecondGradeSqrtMeshWeight]
  dsimp only [n] at hgap hdenpos hden ⊢
  push_cast at hgap hdenpos hden ⊢
  have hgap' : Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1) =
      1 / (Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1)) := by
    convert hgap using 1 <;> ring
  have hdenpos' : 0 <
      Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1) := by
    convert hdenpos using 1 <;> ring
  have hden' : Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1) ≤
      3 * ((k : ℝ) + 1) := by
    convert hden using 1 <;> ring
  rw [hgap', mul_one_div, le_div_iff₀ hdenpos']
  nlinarith

theorem tendsto_selbergSecondGradeSqrtMeshScale_atTop :
    Tendsto selbergSecondGradeSqrtMeshScale atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨K : ℕ, hK⟩ := exists_nat_ge (3 * B)
  refine ⟨K, fun N hKN => ?_⟩
  have hsum : (N : ℝ) * (1 / 3 : ℝ) ≤
      selbergSecondGradeSqrtMeshScale N := by
    have h := Finset.sum_le_sum (s := Finset.range N)
      (fun k _hk => one_third_le_selbergSecondGradeSqrtMeshWeight k)
    simpa [selbergSecondGradeSqrtMeshScale] using h
  have hKNreal : (K : ℝ) ≤ N := by exact_mod_cast hKN
  nlinarith

/-- Toeplitz transport of the sublinear Selberg discrepancy through the exact positive
square-root mesh. -/
theorem tendsto_normalized_selbergSecondGradeSqrtMeshDiscrepancy :
    Tendsto (fun N : ℕ =>
      (selbergSecondGradeSqrtMeshScale N)⁻¹ *
        ∑ k ∈ Finset.range N,
          selbergSecondGradePrefixDiscrepancy (k + 1) *
            (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)))
      atTop (nhds 0) := by
  let y : ℕ → ℝ := fun k =>
    selbergSecondGradePrefixDiscrepancy (k + 1) / ((k + 1 : ℕ) : ℝ)
  let w : ℕ → ℝ := selbergSecondGradeSqrtMeshWeight
  have hy : Tendsto y atTop (nhds 0) := by
    have h := tendsto_selbergSecondGradePrefixDiscrepancy_div.comp
      (tendsto_add_atTop_nat 1)
    change Tendsto (fun k : ℕ =>
      selbergSecondGradePrefixDiscrepancy (k + 1) /
        ((k + 1 : ℕ) : ℝ)) atTop (nhds 0) at h
    exact h
  have hyLittle : y =o[atTop] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr hy
  have herr : (fun k => w k * y k) =o[atTop] w := by
    simpa only [smul_eq_mul, mul_one] using
      (isBigO_refl w atTop).smul_isLittleO hyLittle
  have hsum : (fun N => ∑ k ∈ Finset.range N, w k * y k) =o[atTop]
      (fun N => ∑ k ∈ Finset.range N, w k) := by
    exact herr.sum_range (fun k => selbergSecondGradeSqrtMeshWeight_nonneg k)
      tendsto_selbergSecondGradeSqrtMeshScale_atTop
  have hzero := hsum.tendsto_inv_smul_nhds_zero
  have heq : (fun N : ℕ =>
      ((∑ k ∈ Finset.range N, w k)⁻¹) •
        ∑ k ∈ Finset.range N, w k * y k) =ᶠ[atTop]
      (fun N : ℕ =>
        (selbergSecondGradeSqrtMeshScale N)⁻¹ *
          ∑ k ∈ Finset.range N,
            selbergSecondGradePrefixDiscrepancy (k + 1) *
              (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [w, y, smul_eq_mul, selbergSecondGradeSqrtMeshScale]
    apply congrArg ((∑ k ∈ Finset.range N,
      selbergSecondGradeSqrtMeshWeight k)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro k hk
    have hkpos : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [selbergSecondGradeSqrtMeshWeight]
    field_simp
  simpa only [smul_eq_mul] using hzero.congr' heq

end

end RHTower
