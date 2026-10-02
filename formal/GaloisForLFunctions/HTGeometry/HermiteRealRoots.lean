import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Hermite polynomials have only real, simple roots

Write `g_n = Dⁿ e^{−x²/2} = (−1)ⁿ Heₙ(x) e^{−x²/2}` (`deriv_gaussian_eq_hermite_mul_gaussian`).
Every `g_n` tends to `0` at `±∞`, so Rolle's theorem on half-lines applies
(`exists_hasDerivAt_eq_zero_Ioi`, `exists_hasDerivAt_eq_zero_Iio`).  Between consecutive zeros of
`g_n` and beyond its extreme zeros, `g_{n+1} = g_n′` has a zero.  So the number of distinct real
roots of `Heₙ` increases by at least one at each step, and `Heₙ`, of degree `n`, has `n` distinct
real roots (`card_roots_toFinset_hermite`).  All of its roots are therefore real and simple.
-/

open Polynomial Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Rolle's theorem on half-lines -/

/-- **Rolle on `(a, ∞)`.** If `f a = 0` and `f → 0` at `+∞`, then `f′` vanishes somewhere in
`(a, ∞)`. -/
theorem exists_hasDerivAt_eq_zero_Ioi {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (ha : f a = 0) (hlim : Tendsto f atTop (𝓝 0)) : ∃ c, a < c ∧ f' c = 0 := by
  set φ : ℝ → ℝ := fun u => a + (u - a) / (1 - (u - a)) with hφ
  have hφd : ∀ u ∈ Ioo a (a + 1), HasDerivAt φ (1 / (1 - (u - a)) ^ 2) u := by
    intro u hu
    have hne : 1 - (u - a) ≠ 0 := by have := hu.2; intro h; linarith
    have h1 : HasDerivAt (fun u : ℝ => u - a) 1 u := (hasDerivAt_id u).sub_const a
    have h2 : HasDerivAt (fun u : ℝ => 1 - (u - a)) (-1) u := by
      simpa using h1.const_sub 1
    have h3 := (h1.div h2 hne).const_add a
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hFd : ∀ u ∈ Ioo a (a + 1), HasDerivAt (f ∘ φ) (f' (φ u) * (1 / (1 - (u - a)) ^ 2)) u :=
    fun u hu => (hf (φ u)).comp u (hφd u hu)
  have hleft : Tendsto (f ∘ φ) (𝓝[>] a) (𝓝 0) := by
    have hφc : ContinuousAt φ a := by
      refine continuousAt_const.add (ContinuousAt.div (continuousAt_id.sub continuousAt_const)
        (continuousAt_const.sub (continuousAt_id.sub continuousAt_const)) ?_)
      simp
    have hφa : φ a = a := by simp [hφ]
    have h : ContinuousAt (f ∘ φ) a := ContinuousAt.comp (g := f) (hf (φ a)).continuousAt hφc
    have h2 := h.tendsto
    rw [Function.comp_apply, hφa, ha] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (f ∘ φ) (𝓝[<] (a + 1)) (𝓝 0) := by
    refine hlim.comp ?_
    have hden : Tendsto (fun u : ℝ => 1 - (u - a)) (𝓝[<] (a + 1)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun u : ℝ => 1 - (u - a)) (𝓝 (a + 1)) (𝓝 (1 - (a + 1 - a))) :=
          (continuous_const.sub (continuous_id.sub continuous_const)).tendsto _
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Iio] at hu
        simp only [mem_Ioi]
        linarith
    have hnum : Tendsto (fun u : ℝ => u - a) (𝓝[<] (a + 1)) (𝓝 1) := by
      have : Tendsto (fun u : ℝ => u - a) (𝓝 (a + 1)) (𝓝 (a + 1 - a)) :=
        (continuous_id.sub continuous_const).tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    have hquot : Tendsto (fun u : ℝ => (u - a) * (1 - (u - a))⁻¹) (𝓝[<] (a + 1)) atTop :=
      hnum.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp hden)
    have := tendsto_atTop_add_const_left _ a hquot
    simpa [hφ, div_eq_mul_inv] using this
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero' (by linarith : a < a + 1) hleft hright hFd
  have hpos : 0 < 1 / (1 - (c - a)) ^ 2 := by
    have : 0 < 1 - (c - a) := by linarith [hc.2]
    positivity
  refine ⟨φ c, ?_, (mul_eq_zero.mp hc0).resolve_right hpos.ne'⟩
  have h1 : 0 < c - a := by linarith [hc.1]
  have h2 : 0 < 1 - (c - a) := by linarith [hc.2]
  have : 0 < (c - a) / (1 - (c - a)) := div_pos h1 h2
  simp only [hφ]
  linarith

/-- **Rolle on `(−∞, a)`.** If `f a = 0` and `f → 0` at `−∞`, then `f′` vanishes somewhere in
`(−∞, a)`. -/
theorem exists_hasDerivAt_eq_zero_Iio {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (ha : f a = 0) (hlim : Tendsto f atBot (𝓝 0)) : ∃ c, c < a ∧ f' c = 0 := by
  have hg : ∀ x, HasDerivAt (fun y => f (-y)) (-f' (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
    have h := HasDerivAt.comp x (hf (-x)) h1
    rw [show f' (-x) * -1 = -f' (-x) by ring] at h
    exact h
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero_Ioi (a := -a) hg (by simpa using ha)
    (hlim.comp tendsto_neg_atTop_atBot)
  exact ⟨-c, by linarith, by simpa using hc0⟩

/-! ## Decay of polynomials times the Gaussian -/

theorem tendsto_pow_mul_gaussian_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-(x ^ 2 / 2))) atTop (𝓝 0) := by
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul (Real.exp (1 / 2))
  rw [mul_zero] at hbase
  refine squeeze_zero_norm' ?_ hbase
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hexp : Real.exp (-(x ^ 2 / 2)) ≤ Real.exp (1 / 2) * Real.exp (-x) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x - 1)])
  calc x ^ n * Real.exp (-(x ^ 2 / 2)) ≤ x ^ n * (Real.exp (1 / 2) * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (1 / 2) * (x ^ n * Real.exp (-x)) := by ring

theorem tendsto_eval_mul_gaussian_atTop (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-(x ^ 2 / 2))) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have := hp.add hq
    simpa [add_mul] using this
  | monomial n a =>
    have := (tendsto_pow_mul_gaussian_atTop n).const_mul a
    simpa [mul_assoc] using this

theorem tendsto_eval_mul_gaussian_atBot (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-(x ^ 2 / 2))) atBot (𝓝 0) := by
  have h := (tendsto_eval_mul_gaussian_atTop (p.comp (-X))).comp tendsto_neg_atBot_atTop
  refine h.congr fun x => ?_
  simp

/-! ## The Gaussian derivatives -/

/-- The real Hermite polynomial `Heₙ`. -/
def realHermite (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

theorem aeval_hermite_eq (n : ℕ) (x : ℝ) : aeval x (hermite n) = (realHermite n).eval x := by
  rw [realHermite, eval_map, aeval_def]
  rfl

/-- `g_n = Dⁿ e^{−x²/2}`. -/
def gaussianDeriv (n : ℕ) (x : ℝ) : ℝ := deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x

theorem gaussianDeriv_eq (n : ℕ) (x : ℝ) :
    gaussianDeriv n x = (-1) ^ n * (realHermite n).eval x * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianDeriv, deriv_gaussian_eq_hermite_mul_gaussian, aeval_hermite_eq]

theorem hasDerivAt_gaussianDeriv (n : ℕ) (x : ℝ) :
    HasDerivAt (gaussianDeriv n) (gaussianDeriv (n + 1) x) x := by
  have hfun : gaussianDeriv n = fun y => (-1) ^ n * (realHermite n).eval y *
      Real.exp (-(y ^ 2 / 2)) := funext (gaussianDeriv_eq n)
  have hd : DifferentiableAt ℝ (gaussianDeriv n) x := by
    rw [hfun]
    fun_prop
  have e : deriv (gaussianDeriv n) x = gaussianDeriv (n + 1) x := by
    simp only [gaussianDeriv, Function.iterate_succ_apply']
    rfl
  have h := hd.hasDerivAt
  rwa [e] at h

theorem gaussianDeriv_eq_zero_iff (n : ℕ) (x : ℝ) :
    gaussianDeriv n x = 0 ↔ (realHermite n).eval x = 0 := by
  rw [gaussianDeriv_eq]
  have h1 : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 := Real.exp_pos (-(x ^ 2 / 2))
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact (mul_eq_zero.mp h).resolve_left h1
    · exact absurd h h2.ne'
  · intro h
    rw [h, mul_zero, zero_mul]

theorem tendsto_gaussianDeriv_atTop (n : ℕ) : Tendsto (gaussianDeriv n) atTop (𝓝 0) := by
  have := (tendsto_eval_mul_gaussian_atTop (realHermite n)).const_mul ((-1 : ℝ) ^ n)
  rw [mul_zero] at this
  refine this.congr fun x => ?_
  rw [gaussianDeriv_eq, mul_assoc]

theorem tendsto_gaussianDeriv_atBot (n : ℕ) : Tendsto (gaussianDeriv n) atBot (𝓝 0) := by
  have := (tendsto_eval_mul_gaussian_atBot (realHermite n)).const_mul ((-1 : ℝ) ^ n)
  rw [mul_zero] at this
  refine this.congr fun x => ?_
  rw [gaussianDeriv_eq, mul_assoc]

/-! ## Counting the zeros -/

/-- The finite zero set of `g_n`. -/
def gaussianDerivZeros (n : ℕ) : Finset ℝ := (realHermite n).roots.toFinset

theorem realHermite_ne_zero (n : ℕ) : realHermite n ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [realHermite, natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_hermite,
    natDegree_zero] at this
  have hm := congrArg leadingCoeff h
  rw [realHermite, leadingCoeff_map_of_injective (RingHom.injective_int _), leadingCoeff_hermite,
    leadingCoeff_zero] at hm
  simp at hm

theorem mem_gaussianDerivZeros (n : ℕ) (x : ℝ) :
    x ∈ gaussianDerivZeros n ↔ gaussianDeriv n x = 0 := by
  rw [gaussianDerivZeros, Multiset.mem_toFinset, mem_roots (realHermite_ne_zero n), IsRoot,
    gaussianDeriv_eq_zero_iff]

/-- **One more zero at each step.** If `g_n` has a zero, `g_{n+1}` has at least one more distinct
zero than `g_n`. -/
theorem card_gaussianDerivZeros_succ (n : ℕ) (hne : (gaussianDerivZeros n).Nonempty) :
    (gaussianDerivZeros n).card + 1 ≤ (gaussianDerivZeros (n + 1)).card := by
  classical
  set S := gaussianDerivZeros n
  set T := gaussianDerivZeros (n + 1)
  set lo := S.min' hne
  set hi := S.max' hne
  set T' := T.filter (fun c => lo < c ∧ c < hi)
  -- interior Rolle points
  have hinter : S.card ≤ (T' \ S).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
    have hx0 := (mem_gaussianDerivZeros n x).mp hx
    have hy0 := (mem_gaussianDerivZeros n y).mp hy
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hxy
      (fun u _ => (hasDerivAt_gaussianDeriv n u).continuousAt.continuousWithinAt)
      (by rw [hx0, hy0]) (fun u _ => hasDerivAt_gaussianDeriv n u)
    refine ⟨c, Finset.mem_filter.mpr ⟨(mem_gaussianDerivZeros (n + 1) c).mpr hc0, ?_, ?_⟩,
      hc.1, hc.2⟩
    · exact lt_of_le_of_lt (S.min'_le x hx) hc.1
    · exact lt_of_lt_of_le hc.2 (S.le_max' y hy)
  -- the two outer Rolle points
  obtain ⟨cL, hcL, hcL0⟩ := exists_hasDerivAt_eq_zero_Iio (hasDerivAt_gaussianDeriv n)
    ((mem_gaussianDerivZeros n lo).mp (S.min'_mem hne)) (tendsto_gaussianDeriv_atBot n)
  obtain ⟨cR, hcR, hcR0⟩ := exists_hasDerivAt_eq_zero_Ioi (hasDerivAt_gaussianDeriv n)
    ((mem_gaussianDerivZeros n hi).mp (S.max'_mem hne)) (tendsto_gaussianDeriv_atTop n)
  have hlohi : lo ≤ hi := S.min'_le _ (S.max'_mem hne)
  have hsub : insert cL (insert cR (T' \ S)) ⊆ T := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact (mem_gaussianDerivZeros (n + 1) c).mpr hcL0
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact (mem_gaussianDerivZeros (n + 1) c).mpr hcR0
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1).1
  have hcR_notin : cR ∉ T' \ S := fun h => by
    have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2.2
    linarith
  have hcL_notin : cL ∉ insert cR (T' \ S) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · linarith
    · have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2.1
      linarith
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hcL_notin, Finset.card_insert_of_notMem hcR_notin] at hcard
  omega

theorem zero_mem_gaussianDerivZeros_one : (0 : ℝ) ∈ gaussianDerivZeros 1 := by
  rw [mem_gaussianDerivZeros, gaussianDeriv_eq]
  simp [realHermite]

/-- **`Heₙ` has `n` distinct real roots.** -/
theorem card_roots_toFinset_hermite (n : ℕ) : n ≤ (gaussianDerivZeros n).card := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Finset.card_pos.mpr ⟨0, zero_mem_gaussianDerivZeros_one⟩
    · have hne : (gaussianDerivZeros n).Nonempty := Finset.card_pos.mp (by omega)
      have := card_gaussianDerivZeros_succ n hne
      omega

/-- All roots of `Heₙ` are real and simple: the real root multiset has no repeats and `n` elements. -/
theorem realHermite_roots_nodup_card (n : ℕ) :
    (realHermite n).roots.Nodup ∧ Multiset.card (realHermite n).roots = n := by
  have hdeg : (realHermite n).natDegree = n := by
    rw [realHermite, natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_hermite]
  have h1 := card_roots_toFinset_hermite n
  have h2 : Multiset.card (realHermite n).roots ≤ n := by
    have := card_roots' (realHermite n)
    rwa [hdeg] at this
  have h3 : (gaussianDerivZeros n).card ≤ Multiset.card (realHermite n).roots :=
    Multiset.toFinset_card_le _
  have hcard : Multiset.card (realHermite n).roots = n := by
    unfold gaussianDerivZeros at h1 h3; omega
  refine ⟨?_, hcard⟩
  rw [← Multiset.toFinset_card_eq_card_iff_nodup]
  unfold gaussianDerivZeros at h1 h3
  omega

end

end GaloisForLFunctions.HTGeometry
