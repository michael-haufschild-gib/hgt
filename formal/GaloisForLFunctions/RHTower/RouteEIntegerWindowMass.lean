import GaloisForLFunctions.RHTower.RouteEIntegerComponentAperture
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import GaloisForLFunctions.HTGeometry.BernsteinRowDiagonalKernel

/-!
# Mass of narrow integer-factor windows

Comparable admitted corners differ in at most two changing coordinates. Their
three rank classes are antichains, giving both a Sperner count and a Lubell bound.
The latter bounds an equally oriented Bernoulli window mass by the square root
of an exact squared Bernstein row. A direct dominated-convergence argument lets
both the dimension and the Bernoulli parameter vary. The resulting mass vanishes
at the actual growing marker window when the binomial variance escapes.

The full mixed-orientation histogram transfer and signed Möbius covariance are
separate obligations; this file does not assert either one.
-/

open Finset Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower.IntegerCubeAperture

/-- Product at the corner whose upper factors are indexed by `s`. -/
def cornerProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (s : Finset ι) : ℕ := ∏ i, if i ∈ s then b i else a i

/-- Two admitted endpoints suffice; intermediate corners need not be assumed admitted. -/
theorem comparable_corners_differ_at_most_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (L W : ℝ)
    (ha : ∀ i, 1 ≤ a i) (hab : ∀ i, a i < b i)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hwidth : W^3 < 27*L^2)
    (s t : Finset ι) (hst : s ⊆ t)
    (hs : L ≤ (cornerProduct a b s : ℝ))
    (ht : (cornerProduct a b t : ℝ) ≤ L+W) :
    (t \ s).card ≤ 2 := by
  let low : ι → ℕ := fun i => if i ∈ s then b i else a i
  let high : ι → ℕ := fun i => if i ∈ t then b i else a i
  have hlow (i : ι) (_ : i ∈ (univ : Finset ι)) : 1 ≤ low i := by
    dsimp [low]
    split_ifs <;> have := ha i <;> have := hab i <;> omega
  have hle (i : ι) (_ : i ∈ (univ : Finset ι)) : low i ≤ high i := by
    dsimp [low,high]
    split_ifs with h1 h2 h2
    · rfl
    · exact False.elim (h2 (hst h1))
    · exact (hab i).le
    · rfl
  have h := at_most_two_changes_real_window univ low high L W
    hlow hle hL hW hs ht hwidth
  have he : (univ.filter fun i => low i < high i) = t \ s := by
    ext i
    simp only [mem_filter,mem_univ,true_and]
    dsimp [low,high]
    by_cases h1 : i ∈ s
    · simp [h1,hst h1]
    · by_cases h2 : i ∈ t <;> simp [h1,h2,hab i]
  rwa [he] at h

/-- Rank modulo three partitions the admitted family into antichains. -/
theorem rank_mod_three_isAntichain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (Finset ι))
    (hA : ∀ s ∈ A, ∀ t ∈ A, s ⊆ t → (t \ s).card ≤ 2) (r : ℕ) :
    IsAntichain (· ⊆ ·) (A.filter (fun s => s.card % 3 = r) : Set (Finset ι)) := by
    intro s hs t ht hne hst
    obtain ⟨hsA,hsr⟩ := mem_filter.mp hs
    obtain ⟨htA,htr⟩ := mem_filter.mp ht
    have hdiff := hA s hsA t htA hst
    rw [card_sdiff_of_subset hst] at hdiff
    have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hst,hne⟩)
    omega

theorem three_antichain_card_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (Finset ι))
    (hA : ∀ s ∈ A, ∀ t ∈ A, s ⊆ t → (t \ s).card ≤ 2) :
    A.card ≤ 3*(Fintype.card ι).choose (Fintype.card ι / 2) := by
  let layer (r : ℕ) := A.filter fun s => s.card % 3 = r
  have hanti (r : ℕ) : IsAntichain (· ⊆ ·) (layer r : Set (Finset ι)) :=
    rank_mod_three_isAntichain A hA r
  have hcard (r : ℕ) := (hanti r).sperner
  have he : A = layer 0 ∪ layer 1 ∪ layer 2 := by
    ext s
    by_cases hs : s ∈ A
    · have hr : s.card % 3 = 0 ∨ s.card % 3 = 1 ∨ s.card % 3 = 2 := by omega
      simpa [layer,hs,or_assoc] using hr
    · simp [layer,hs]
  rw [he]
  have h01 := card_union_le (layer 0) (layer 1)
  have h012 := card_union_le (layer 0 ∪ layer 1) (layer 2)
  have h0 := hcard 0
  have h1 := hcard 1
  have h2 := hcard 2
  omega

theorem integer_window_card_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (L W : ℝ)
    (ha : ∀ i, 1 ≤ a i) (hab : ∀ i, a i < b i)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hwidth : W^3 < 27*L^2) :
    (univ.filter fun s : Finset ι => (cornerProduct a b s : ℝ) ∈ Set.Icc L (L+W)).card ≤
      3*(Fintype.card ι).choose (Fintype.card ι / 2) := by
  apply three_antichain_card_bound
  intro s hs t ht hst
  exact comparable_corners_differ_at_most_two a b L W ha hab hL hW hwidth
    s t hst (mem_filter.mp hs).2.1 (mem_filter.mp ht).2.2

theorem three_antichain_lubell_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (Finset ι))
    (hA : ∀ s ∈ A, ∀ t ∈ A, s ⊆ t → (t \ s).card ≤ 2) :
    ∑ s ∈ A, (((Fintype.card ι).choose s.card : ℕ) : ℝ)⁻¹ ≤ 3 := by
  have hm : ∀ s ∈ A, s.card % 3 ∈ range 3 := by
    intro s _
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  rw [← sum_fiberwise_of_maps_to hm]
  calc
    _ ≤ ∑ _r ∈ range 3, (1:ℝ) := by
      apply sum_le_sum
      intro r hr
      exact lubell_yamamoto_meshalkin_inequality_sum_inv_choose
        (rank_mod_three_isAntichain A hA r)
    _ = 3 := by simp

theorem binomial_atom_le_sqrt_row (n k : ℕ) (p : ℝ) (hk : k ≤ n) :
    (n.choose k : ℝ)*p^k*(1-p)^(n-k) ≤
      Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare p (1-p) n) := by
  have hs : ((n.choose k : ℝ)*p^k*(1-p)^(n-k))^2 ≤
      GaloisForLFunctions.HTGeometry.bernsteinRowSquare p (1-p) n := by
    have h := single_le_sum (f := fun j => ((n.choose j : ℝ)*p^j*(1-p)^(n-j))^2)
      (fun j _ => sq_nonneg _) (show k ∈ range (n+1) by simpa using hk)
    refine h.trans_eq ?_
    unfold GaloisForLFunctions.HTGeometry.bernsteinRowSquare
    apply sum_congr rfl
    intro j hj
    ring
  by_cases ha : 0 ≤ (n.choose k : ℝ)*p^k*(1-p)^(n-k)
  · exact (Real.le_sqrt ha ((sq_nonneg _).trans hs)).mpr hs
  · exact (le_of_lt (lt_of_not_ge ha)).trans (Real.sqrt_nonneg _)

theorem three_antichain_bernoulli_mass_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (Finset ι)) (p : ℝ)
    (hA : ∀ s ∈ A, ∀ t ∈ A, s ⊆ t → (t \ s).card ≤ 2) :
    ∑ s ∈ A, p^s.card*(1-p)^(Fintype.card ι-s.card) ≤
      3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare
        p (1-p) (Fintype.card ι)) := by
  let C := Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare
    p (1-p) (Fintype.card ι))
  calc
    _ ≤ ∑ s ∈ A, C*(((Fintype.card ι).choose s.card : ℕ):ℝ)⁻¹ := by
      apply sum_le_sum
      intro s hs
      have hc : (0:ℝ) < ((Fintype.card ι).choose s.card : ℕ) := by
        exact_mod_cast Nat.choose_pos s.card_le_univ
      have hb := binomial_atom_le_sqrt_row (Fintype.card ι) s.card p s.card_le_univ
      exact (le_mul_inv_iff₀ hc).mpr (by simpa [C,mul_assoc,mul_left_comm,mul_comm] using hb)
    _ = C*∑ s ∈ A, (((Fintype.card ι).choose s.card : ℕ):ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ C*3 := mul_le_mul_of_nonneg_left (three_antichain_lubell_bound A hA) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem integer_window_bernoulli_mass_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (L W p : ℝ)
    (ha : ∀ i, 1 ≤ a i) (hab : ∀ i, a i < b i)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hwidth : W^3 < 27*L^2) :
    ∑ s ∈ (univ.filter fun s : Finset ι => (cornerProduct a b s : ℝ) ∈ Set.Icc L (L+W)),
        p^s.card*(1-p)^(Fintype.card ι-s.card) ≤
      3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare
        p (1-p) (Fintype.card ι)) := by
  apply three_antichain_bernoulli_mass_bound
  intro s hs t ht hst
  exact comparable_corners_differ_at_most_two a b L W ha hab hL hW hwidth
    s t hst (mem_filter.mp hs).2.1 (mem_filter.mp ht).2.2

theorem aperture_div_spectator (L W c : ℝ) (hc : 1 ≤ c)
    (hwidth : W^3 < 27*L^2) : (W/c)^3 < 27*(L/c)^2 := by
  have hc0 : 0 < c := by linarith
  rw [div_pow,div_pow]
  apply (div_lt_iff₀ (pow_pos hc0 3)).mpr
  have he : 27*(L^2/c^2)*c^3 = 27*L^2*c := by field_simp
  rw [he]
  exact hwidth.trans_le (le_mul_of_one_le_right (by positivity) hc)

/-- A spectator of size at least one preserves the same mass bound. -/
theorem integer_window_spectator_bernoulli_mass_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (L W c p : ℝ)
    (ha : ∀ i, 1 ≤ a i) (hab : ∀ i, a i < b i)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hc : 1 ≤ c) (hwidth : W^3 < 27*L^2) :
    ∑ s ∈ (univ.filter fun s : Finset ι => c*(cornerProduct a b s : ℝ) ∈ Set.Icc L (L+W)),
        p^s.card*(1-p)^(Fintype.card ι-s.card) ≤
      3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare
        p (1-p) (Fintype.card ι)) := by
  have hc0 : 0 < c := by linarith
  have he : (univ.filter fun s : Finset ι => c*(cornerProduct a b s : ℝ) ∈ Set.Icc L (L+W)) =
      (univ.filter fun s : Finset ι => (cornerProduct a b s : ℝ) ∈ Set.Icc (L/c) (L/c+W/c)) := by
    ext s
    simp only [mem_filter,mem_univ,true_and,Set.mem_Icc]
    rw [div_le_iff₀ hc0,← add_div,le_div_iff₀ hc0]
    simp only [mul_comm]
  rw [he]
  exact integer_window_bernoulli_mass_bound a b (L/c) (W/c) p ha hab
    (div_nonneg hL hc0.le) (div_nonneg hW hc0.le) (aperture_div_spectator L W c hc hwidth)


open GaloisForLFunctions.HTGeometry


theorem one_sub_pow_le_reciprocal (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    (1-u)^n ≤ (1+(n:ℝ)*u)⁻¹ := by
  have h (n : ℕ) : (1-u)^n*(1+(n:ℝ)*u) ≤ 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 0 ≤ (n+1:ℝ)*u^2 := by positivity
      have hp : 0 ≤ (1-u)^n := pow_nonneg (by linarith) _
      have hmul := mul_nonneg hp hn
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith
  have hpos : 0 < 1+(n:ℝ)*u := by positivity
  rw [← one_div]
  exact (le_div_iff₀ hpos).mpr (h n)

private def binomialTrig (n : ℕ) (p x : ℝ) : ℝ :=
  (1-4*p*(1-p)*Real.sin x^2)^n

private theorem binomialTrig_base_bounds (p x : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ 1-4*p*(1-p)*Real.sin x^2 ∧ 1-4*p*(1-p)*Real.sin x^2 ≤ 1 := by
  have hs := Real.sin_sq_add_cos_sq x
  have hprod : 0 ≤ 4*p*(1-p)*Real.sin x^2 := by positivity
  have hid : 1-4*p*(1-p)*Real.sin x^2 =
      (2*p-1)^2*Real.sin x^2+Real.cos x^2 := by nlinarith [hs]
  constructor
  · rw [hid]; positivity
  · linarith

/-- Binomial concentration with varying dimension and bias, from the exact source integral. -/
theorem tendsto_binomial_rowSquare_zero (d : ℕ → ℕ) (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hvariance : Tendsto (fun n => (d n:ℝ)*p n*(1-p n)) atTop atTop) :
    Tendsto (fun n => bernsteinRowSquare (p n) (1-p n) (d n)) atTop (𝓝 0) := by
  let μ := volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2))
  have hbound : Integrable (fun _ : ℝ => (1:ℝ)) μ := by
    dsimp [μ]
    exact integrable_const _
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (binomialTrig (d n) (p n)) μ := by
    filter_upwards with n
    have hc : Continuous (binomialTrig (d n) (p n)) := by unfold binomialTrig; fun_prop
    exact hc.aestronglyMeasurable
  have hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, ‖binomialTrig (d n) (p n) x‖ ≤ 1 := by
    filter_upwards with n
    filter_upwards with x
    obtain ⟨h0,h1⟩ := binomialTrig_base_bounds (p n) x (hp n).1 (hp n).2
    rw [binomialTrig,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg h0 _)]
    exact pow_le_one₀ h0 h1
  have hptw : ∀ᵐ x ∂μ, Tendsto (fun n => binomialTrig (d n) (p n) x) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hspos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_pos])
    have ht := Filter.Tendsto.const_mul_atTop (show 0 < 4*Real.sin x^2 by positivity) hvariance
    have ht' : Tendsto (fun n => 1+(d n:ℝ)*(4*p n*(1-p n)*Real.sin x^2)) atTop atTop := by
      have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      convert hc.add_atTop ht using 1
      funext n
      ring
    have hinv := tendsto_inv_atTop_zero.comp ht'
    apply squeeze_zero (fun n => ?_) (fun n => ?_) hinv
    · exact pow_nonneg (binomialTrig_base_bounds (p n) x (hp n).1 (hp n).2).1 _
    · have hp0 := (hp n).1
      have hp1 := (hp n).2
      exact one_sub_pow_le_reciprocal _ (by positivity)
        (by have := (binomialTrig_base_bounds (p n) x (hp n).1 (hp n).2).1; linarith) _
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => (1:ℝ)) hmeas hdom hbound hptw
  simp only [integral_zero] at hdct
  have hquarter (n : ℕ) : bernsteinRowSquare (p n) (1-p n) (d n) =
      (2/Real.pi)*(∫ x, binomialTrig (d n) (p n) x ∂μ) := by
    rw [bernsteinRowSquare_eq_centralBinomialDiagonalKernelCoefficient,
      ← quarterIntegral_quadraticPow_eq_centralBinomialDiagonalKernelCoefficient]
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    unfold binomialTrig
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hscaled := hdct.const_mul (2/Real.pi)
  simpa only [mul_zero,← hquarter] using hscaled


/-- Equally oriented integer factors have vanishing admitted mass at the actual growing window. -/
theorem tendsto_growing_window_bernoulli_mass_zero
    (d : ℕ → ℕ) (a b : ∀ n, Fin (d n) → ℕ) (X c p : ℕ → ℝ)
    (ha : ∀ n i, 1 ≤ a n i) (hab : ∀ n i, a n i < b n i)
    (hc : ∀ n, 1 ≤ c n) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hX : Tendsto X atTop atTop)
    (hvariance : Tendsto (fun n => (d n:ℝ)*p n*(1-p n)) atTop atTop) :
    Tendsto (fun n =>
      ∑ s ∈ (univ.filter fun s : Finset (Fin (d n)) =>
        c n*(cornerProduct (a n) (b n) s : ℝ) ∈
          Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
            (X n+Sieve.growingReciprocalMarkerWindow (X n))),
        p n^s.card*(1-p n)^(d n-s.card)) atTop (𝓝 0) := by
  have hnonneg (n : ℕ) : 0 ≤
      ∑ s ∈ (univ.filter fun s : Finset (Fin (d n)) =>
        c n*(cornerProduct (a n) (b n) s : ℝ) ∈
          Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
            (X n+Sieve.growingReciprocalMarkerWindow (X n))),
        p n^s.card*(1-p n)^(d n-s.card) := by
    have hp0 := (hp n).1
    have hp1 := (hp n).2
    apply sum_nonneg
    intros
    positivity
  have hupper : ∀ᶠ n in atTop,
      (∑ s ∈ (univ.filter fun s : Finset (Fin (d n)) =>
        c n*(cornerProduct (a n) (b n) s : ℝ) ∈
          Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
            (X n+Sieve.growingReciprocalMarkerWindow (X n))),
        p n^s.card*(1-p n)^(d n-s.card)) ≤
        3*Real.sqrt (bernsteinRowSquare (p n) (1-p n) (d n)) := by
    filter_upwards [hX.eventually growing_window_aperture] with n hn
    have hw : X n-Sieve.growingReciprocalMarkerWindow (X n)+
        2*Sieve.growingReciprocalMarkerWindow (X n) =
        X n+Sieve.growingReciprocalMarkerWindow (X n) := by ring
    simpa only [hw,Fintype.card_fin] using
      integer_window_spectator_bernoulli_mass_bound (a n) (b n)
        (X n-Sieve.growingReciprocalMarkerWindow (X n))
        (2*Sieve.growingReciprocalMarkerWindow (X n)) (c n) (p n)
        (ha n) (hab n) (by linarith [hn.2.1]) (by linarith [hn.1]) (hc n) hn.2.2
  have hlimit := ((tendsto_binomial_rowSquare_zero d p hp hvariance).sqrt).const_mul (3:ℝ)
  apply squeeze_zero' (Eventually.of_forall hnonneg) hupper
  simpa only [Real.sqrt_zero,mul_zero] using hlimit

end RHTower.IntegerCubeAperture
