import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowDirichletAlgebra
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The reflection centralizer of the window algebra

The truncated Dirichlet representation moves functions only toward the right endpoint.
Commutation with Serre reflection therefore forces every positive shift coefficient to vanish.
The intersection of this algebra with its reflection centralizer consists exactly of scalars.
Endpoint vectors detect every active coefficient. Smooth tests detect precisely the shifts
strictly shorter than the window; full-length shifts vanish on continuous tests.
Neither classification uses positivity of Weil's form.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

/-- Killing all positive shifts leaves scalar multiplication on the window module. -/
theorem windowRepFun_eq_scalar_of_positive_coefficients_zero {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) (hf : ∀ n ∈ Finset.Icc 2 (windowLevel A), f n = 0)
    {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    windowRepFun A f H = fun u => f 1 * H u := by
  have h1 : 1 ∈ Finset.Icc 1 (windowLevel A) := Finset.mem_Icc.mpr ⟨le_rfl, by
    rw [windowLevel, Nat.le_floor_iff (Real.exp_pos A).le]
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hA⟩
  funext u
  rw [windowRepFun, Finset.sum_eq_single_of_mem 1 h1]
  · simp only [Nat.cast_one, Real.sqrt_one, div_one, Real.log_one, windowShift_zero hH]
  · intro n hn hn1
    rw [hf n (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega,
      (Finset.mem_Icc.mp hn).2⟩), zero_div, zero_mul]

/-- Serre reflection commutes with a truncated Dirichlet operator exactly when its
coefficients at every active integer `n ≥ 2` vanish. -/
theorem windowRepFun_commutes_reflection_iff {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) :
    (∀ H ∈ windowSupported A,
      windowInvolution A (windowRepFun A f H) =
        windowRepFun A f (windowInvolution A H)) ↔
      ∀ n ∈ Finset.Icc 2 (windowLevel A), f n = 0 := by
  constructor
  · intro hcomm n hn
    have hn1 : n ∈ Finset.Icc 1 (windowLevel A) :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega,
        (Finset.mem_Icc.mp hn).2⟩
    have hlog : 0 < Real.log n := Real.log_pos (by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (show 1 < n by omega))
    have hright : windowRepFun A f (windowInvolution A (leftEndPoint A))
        (-Real.log n) = 0 := by
      rw [windowRepFun]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [windowShift_apply_of_le _ (by linarith)]
      have hlogk := (log_le_of_mem_Icc_one hk).1
      have hz : windowInvolution A (leftEndPoint A) (-Real.log n - Real.log k) = 0 := by
        unfold windowInvolution leftEndPoint
        apply indicator_of_notMem
        intro heq
        have := mem_singleton_iff.mp heq
        linarith
      rw [hz, mul_zero]
    have heq := congrFun (hcomm (leftEndPoint A) (leftEndPoint_mem hA)) (-Real.log n)
    rw [windowInvolution, show -A - -Real.log n = Real.log n - A by ring,
      windowRepFun_leftEndPoint f hn1, hright] at heq
    exact (div_eq_zero_iff.mp heq).resolve_right
      (Real.sqrt_pos.mpr (by exact_mod_cast (Finset.mem_Icc.mp hn1).1)).ne'
  · intro hf H hH
    have hσ : windowInvolution A H ∈ windowSupported A := fun y hy =>
      hH _ fun hm => hy ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [windowRepFun_eq_scalar_of_positive_coefficients_zero hA f hf hH,
      windowRepFun_eq_scalar_of_positive_coefficients_zero hA f hf hσ]
    rfl

/-- The centralizer classification in operator form: only scalar window actions commute
with Serre reflection inside the Dirichlet representation. -/
theorem windowRepFun_commutes_reflection_iff_scalar {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) :
    (∀ H ∈ windowSupported A,
      windowInvolution A (windowRepFun A f H) =
        windowRepFun A f (windowInvolution A H)) ↔
      ∀ H ∈ windowSupported A, windowRepFun A f H = fun u => f 1 * H u := by
  constructor
  · intro h H hH
    exact windowRepFun_eq_scalar_of_positive_coefficients_zero hA f
      ((windowRepFun_commutes_reflection_iff hA f).mp h) hH
  · intro h H hH
    have hσ : windowInvolution A H ∈ windowSupported A := fun y hy =>
      hH _ fun hm => hy ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [h H hH, h _ hσ]
    rfl

#print axioms windowRepFun_commutes_reflection_iff
#print axioms windowRepFun_commutes_reflection_iff_scalar

/-- A continuous function supported on a closed window vanishes at both endpoints. -/
theorem support_subset_open_window {A : ℝ} {H : ℝ → ℝ}
    (hc : Continuous H) (hH : H ∈ windowSupported A) :
    Function.support H ⊆ Set.Ioo (-A) 0 := by
  have hs : Function.support H ⊆ Set.Icc (-A) 0 := fun u hu => by
    by_contra h
    exact hu (hH u h)
  have ho : IsOpen (Function.support H) :=
    isOpen_compl_singleton.preimage hc
  simpa only [interior_Icc] using interior_maximal hs ho

/-- A shift reaching the full window length already annihilates continuous tests. -/
theorem windowShift_eq_zero_of_length_le {A t : ℝ} {H : ℝ → ℝ}
    (hc : Continuous H) (hH : H ∈ windowSupported A) (ht : A ≤ t) :
    windowShift t H = 0 := by
  funext u
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu]
    change H (u - t) = 0
    by_contra hn
    have hm := support_subset_open_window hc hH hn
    linarith [hm.1]
  · exact windowShift_apply_of_pos _ hu

/-- Smooth tests detect every coefficient strictly inside the window, despite the vanishing
of all endpoint values. A bump separates the finitely many forward and reflected sample points. -/
theorem positive_coefficients_zero_of_smooth_reflection_commutation {A : ℝ}
    (f : ArithmeticFunction ℝ)
    (hcomm : ∀ H, IsWindowTest A H →
      windowInvolution A (windowRepFun A f H) =
        windowRepFun A f (windowInvolution A H))
    {n : ℕ} (hn : 2 ≤ n) (hnA : Real.log n < A) : f n = 0 := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hnN : n ≤ windowLevel A := by
    rw [windowLevel, Nat.le_floor_iff (Real.exp_pos A).le]
    exact ((Real.log_lt_iff_lt_exp hn0).mp hnA).le
  let K := Finset.Icc 1 (windowLevel A)
  have hnK : n ∈ K := Finset.mem_Icc.mpr ⟨by omega, hnN⟩
  let c := -(A + Real.log n) / 2
  let x := (Real.log n - A) / 2
  have hx : x < 0 := by dsimp [x]; linarith
  have hc : c ∈ Set.Ioo (-A) 0 := by
    dsimp [c]; constructor <;> linarith
  have hcx : -A - c = x := by dsimp [c, x]; ring
  have hxc : x - Real.log n = c := by dsimp [c, x]; ring
  let S := (K.erase n).image (fun k : ℕ => x - Real.log k) ∪
    K.image (fun k : ℕ => x + Real.log k)
  have hcS : c ∉ S := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm
      obtain ⟨hkn, hkK⟩ := Finset.mem_erase.mp hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hkK).1
      have heqlog : Real.log k = Real.log n := by rw [← hxc] at heq; linarith
      exact hkn (by exact_mod_cast Real.log_injOn_pos hk0 hn0 heqlog)
    · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm
      have hklog := (log_le_of_mem_Icc_one hk).1
      rw [← hxc] at heq
      linarith
  let U := Set.Ioo (-A) 0 \ (S : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.inter S.finite_toSet.isClosed.isOpen_compl
  have hcU : c ∈ U := ⟨hc, hcS⟩
  obtain ⟨H, hsupp, hdiff, -⟩ := hU.exists_contDiff_support_eq (n := 2)
  have hH : IsWindowTest A H := by
    refine ⟨hdiff, ?_⟩
    intro y hy
    by_contra hne
    have hm : y ∈ U := hsupp ▸ hne
    exact hy ⟨hm.1.1.le, hm.1.2.le⟩
  have hHc : H c ≠ 0 := by
    change c ∈ Function.support H
    rw [hsupp]
    exact hcU
  have hzero (y : ℝ) (hy : y ∈ S) : H y = 0 := by
    by_contra hnz
    have hm : y ∈ U := hsupp ▸ hnz
    exact hm.2 hy
  have hleft : windowRepFun A f H x = f n / Real.sqrt n * H c := by
    rw [windowRepFun, Finset.sum_eq_single_of_mem n hnK]
    · rw [windowShift_apply_of_le _ hx.le, hxc]
    · intro k hk hkn
      rw [windowShift_apply_of_le _ hx.le,
        hzero _ (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨k, Finset.mem_erase.mpr ⟨hkn, hk⟩, rfl⟩)), mul_zero]
  have hright : windowRepFun A f (windowInvolution A H) c = 0 := by
    rw [windowRepFun]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [windowShift_apply_of_le _ hc.2.le]
    have hpoint : windowInvolution A H (c - Real.log k) = H (x + Real.log k) := by
      unfold windowInvolution
      congr 1
      rw [show -A - (c - Real.log k) = (-A - c) + Real.log k by ring, hcx]
    rw [hpoint, hzero _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨k, hk, rfl⟩)), mul_zero]
  have heq := congrFun (hcomm H hH) c
  change windowRepFun A f H (-A - c) = _ at heq
  rw [hcx, hleft, hright] at heq
  exact (div_eq_zero_iff.mp ((mul_eq_zero.mp heq).resolve_right hHc)).resolve_right
    (Real.sqrt_pos.mpr hn0).ne'

/-- On continuous windows, coefficients at the exact stage boundary act by zero. -/
theorem windowRepFun_eq_scalar_of_interior_coefficients_zero {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) (hf : ∀ n : ℕ, 2 ≤ n → Real.log n < A → f n = 0)
    {H : ℝ → ℝ} (hc : Continuous H) (hH : H ∈ windowSupported A) :
    windowRepFun A f H = fun u => f 1 * H u := by
  have h1 : 1 ∈ Finset.Icc 1 (windowLevel A) := Finset.mem_Icc.mpr ⟨le_rfl, by
    rw [windowLevel, Nat.le_floor_iff (Real.exp_pos A).le]
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hA⟩
  funext u
  rw [windowRepFun, Finset.sum_eq_single_of_mem 1 h1]
  · simp only [Nat.cast_one, Real.sqrt_one, div_one, Real.log_one, windowShift_zero hH]
  · intro n hn hn1
    by_cases hlt : Real.log n < A
    · rw [hf n (by have := (Finset.mem_Icc.mp hn).1; omega) hlt, zero_div, zero_mul]
    · rw [windowShift_eq_zero_of_length_le hc hH (le_of_not_gt hlt), Pi.zero_apply, mul_zero]

/-- On the smooth window test space, the reflection centralizer still consists of scalar
operators. The coefficient condition omits shifts exactly at the full window length. -/
theorem smooth_windowRepFun_commutes_reflection_iff {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) :
    (∀ H, IsWindowTest A H →
      windowInvolution A (windowRepFun A f H) =
        windowRepFun A f (windowInvolution A H)) ↔
      ∀ n : ℕ, 2 ≤ n → Real.log n < A → f n = 0 := by
  constructor
  · intro h n hn hnA
    exact positive_coefficients_zero_of_smooth_reflection_commutation f h hn hnA
  · intro hf H hH
    have hσ := hH.windowInvolution
    rw [windowRepFun_eq_scalar_of_interior_coefficients_zero hA f hf hH.continuous hH.vanish,
      windowRepFun_eq_scalar_of_interior_coefficients_zero hA f hf hσ.continuous hσ.vanish]
    rfl

/-- The smooth reflection centralizer acts by the coefficient at `1`, with no other action. -/
theorem smooth_windowRepFun_commutes_reflection_iff_scalar {A : ℝ} (hA : 0 ≤ A)
    (f : ArithmeticFunction ℝ) :
    (∀ H, IsWindowTest A H →
      windowInvolution A (windowRepFun A f H) =
        windowRepFun A f (windowInvolution A H)) ↔
      ∀ H, IsWindowTest A H → windowRepFun A f H = fun u => f 1 * H u := by
  constructor
  · intro h H hH
    exact windowRepFun_eq_scalar_of_interior_coefficients_zero hA f
      ((smooth_windowRepFun_commutes_reflection_iff hA f).mp h) hH.continuous hH.vanish
  · intro h H hH
    rw [h H hH, h _ hH.windowInvolution]
    rfl

#print axioms smooth_windowRepFun_commutes_reflection_iff
#print axioms smooth_windowRepFun_commutes_reflection_iff_scalar

end GaloisForLFunctions.WindowTowerOfSpecZ
