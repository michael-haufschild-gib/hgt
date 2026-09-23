import GaloisForLFunctions.HTGeometry.JumpProfileLevels
import GaloisForLFunctions.HTGeometry.UnimodularWindowMoments

/-!
# One window of the remainder recursion

Assigning unimodular phases with prescribed weights to a family of nodes inside a window replaces
the level vector of the remainder chain by the rounding error of the moment problem.  This is the
inductive step of an Andersson-type recursion: the Taylor image of the old levels is cancelled by
the window moments, and only the `J · C` rounding error survives, scaled by `Δ^j / j!`.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The source built from a node family, a phase and a weight. -/
def windowAssign {N : ℕ} (p : Fin N → ℕ) (b : Fin N → ℂ) (w : Fin N → ℝ) : ℕ → ℂ :=
  fun n => if h : ∃ r, p r = n then b h.choose * ((w h.choose : ℝ) : ℂ) else 0

theorem windowAssign_apply {N : ℕ} {p : Fin N → ℕ} (hinj : Function.Injective p)
    (b : Fin N → ℂ) (w : Fin N → ℝ) (r : Fin N) :
    windowAssign p b w (p r) = b r * ((w r : ℝ) : ℂ) := by
  have hex : ∃ r', p r' = p r := ⟨r, rfl⟩
  rw [windowAssign, dif_pos hex]
  have : hex.choose = r := hinj hex.choose_spec
  rw [this]

theorem windowAssign_of_notMem {N : ℕ} (p : Fin N → ℕ) (b : Fin N → ℂ) (w : Fin N → ℝ) {n : ℕ}
    (hn : ∀ r, p r ≠ n) : windowAssign p b w n = 0 := by
  rw [windowAssign, dif_neg]
  rintro ⟨r, hr⟩
  exact hn r hr

theorem sum_windowAssign {N : ℕ} {p : Fin N → ℕ} (hinj : Function.Injective p)
    (b : Fin N → ℂ) (w : Fin N → ℝ) {S : Finset ℕ} (hp : ∀ r, p r ∈ S) (f : ℕ → ℂ) :
    (∑ n ∈ S, windowAssign p b w n * f n)
      = ∑ r : Fin N, b r * ((w r : ℝ) : ℂ) * f (p r) := by
  classical
  have himg : (Finset.univ.image p) ⊆ S := by
    intro n hn
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hn
    exact hp r
  have hzero : ∀ n ∈ S, n ∉ Finset.univ.image p → windowAssign p b w n * f n = 0 := by
    intro n _ hnot
    have : ∀ r, p r ≠ n := by
      intro r hr
      exact hnot (Finset.mem_image.2 ⟨r, Finset.mem_univ r, hr⟩)
    rw [windowAssign_of_notMem p b w this, zero_mul]
  rw [← Finset.sum_subset himg hzero,
    Finset.sum_image (fun r _ r' _ h => hinj h)]
  exact Finset.sum_congr rfl fun r _ => by rw [windowAssign_apply hinj b w r]

/-- The Taylor image at `y` of the levels at the base point `x`. -/
def windowTaylor (a : ℕ → ℂ) (x y : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (j + 1),
    (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * arithProfile a m x

/-- The moment vector the window must realize in order to cancel the Taylor image. -/
def windowTarget (a : ℕ → ℂ) (x y : ℝ) (j : ℕ) : ℂ :=
  -((((j.factorial : ℕ) : ℝ) / (y - x) ^ j : ℝ) : ℂ) * windowTaylor a x y j

/-- The window nodes normalized to `[0,1]`. -/
def windowNode {N : ℕ} (p : Fin N → ℕ) (x y : ℝ) : Fin N → ℝ :=
  fun r => (y - (p r : ℝ)) / (y - x)

theorem windowNode_mem_Icc {N : ℕ} {p : Fin N → ℕ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y)
    (hp : ∀ r, p r ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (r : Fin N) :
    windowNode p x y r ∈ Set.Icc (0:ℝ) 1 := by
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hy0 : (0:ℝ) ≤ y := le_trans hx0 (le_of_lt hxy)
  have hD : 0 < y - x := by linarith
  have hmem := Finset.mem_Ioc.1 (hp r)
  have hup : (p r : ℝ) ≤ y := by
    have h1 : (p r : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
    exact le_trans h1 (Nat.floor_le hy0)
  have hlow : x < (p r : ℝ) := by
    have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (p r : ℝ) := by exact_mod_cast hmem.1
    have h2 := Nat.lt_floor_add_one x
    linarith
  constructor
  · rw [windowNode]
    exact div_nonneg (by linarith) (le_of_lt hD)
  · rw [windowNode, div_le_one hD]
    linarith

/-- **The window step.**  With enough weighted nodes in the window — a Rayleigh floor for their
moment matrix — unimodular phases can be assigned so that every level of the remainder chain at the
right endpoint is bounded by the rounding error, scaled by `Δ^j / j!`. -/
theorem exists_window_phases {N J : ℕ} (hJ : 0 < J) (a : ℕ → ℂ) {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) {p : Fin N → ℕ} (hinj : Function.Injective p)
    (hp : ∀ r, p r ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (w : Fin N → ℝ) {C : ℝ} (hC : ∀ r, |w r| ≤ C)
    (hC0 : 0 ≤ C) {lam : ℝ} (hlam : 0 < lam)
    (hquad : ∀ u : Fin J → ℝ,
      lam * (∑ i, u i ^ (2 : ℕ)) ≤ u ⬝ᵥ (atomicHankel w (windowNode p x y) J).mulVec u)
    (hsize : (J : ℝ) * (∑ j : Fin J, ‖2 * windowTarget a x y (j : ℕ)‖ ^ (2 : ℕ)) ≤ lam ^ (2 : ℕ)) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J,
        ‖arithProfile (updateWindow a (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (windowAssign p b w)) (j : ℕ) y‖
          ≤ ((y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ)) * ((J : ℝ) * C) := by
  classical
  have hD : 0 < y - x := by linarith
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_window_moments_complex hJ hlam
    (windowNode p x y) w (windowNode_mem_Icc hx hxy hp) hC hC0 hquad
    (fun j => windowTarget a x y (j : ℕ)) hsize
  refine ⟨b, hb1, fun j => ?_⟩
  have hfac : (0:ℝ) < (((j : ℕ).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j : ℕ)
  have hDj : (0:ℝ) < (y - x) ^ (j : ℕ) := pow_pos hD _
  set κ : ℝ := (y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) with hκ
  have hκpos : 0 < κ := by
    rw [hκ]
    exact div_pos hDj hfac
  have hstep := arithProfile_updateWindow_step a (windowAssign p b w) (j : ℕ) hx (le_of_lt hxy)
  have hwindow : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, windowAssign p b w n
        * (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ))
      = (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ) := by
    rw [sum_windowAssign hinj b w hp
      (fun n => (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hnode : (y - (p r : ℝ)) = (y - x) * windowNode p x y r := by
      rw [windowNode]
      field_simp
    rw [hnode, hκ, windowNode]
    push_cast
    rw [mul_pow]
    field_simp
  have hone : ((κ : ℝ) : ℂ)
      * (((((j : ℕ).factorial : ℕ) : ℝ) / (y - x) ^ (j : ℕ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hκ]
    norm_cast
    field_simp
  have htaylor : (κ : ℂ) * windowTarget a x y (j : ℕ) = -windowTaylor a x y (j : ℕ) := by
    rw [windowTarget, ← mul_assoc, mul_neg, hone, neg_one_mul]
  rw [hstep, ← windowTaylor, hwindow]
  have hcollect : windowTaylor a x y (j : ℕ)
      + (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ)
      = (κ : ℂ) * ((∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ))
          - windowTarget a x y (j : ℕ)) := by
    rw [mul_sub, htaylor]
    ring
  rw [hcollect, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
  exact mul_le_mul_of_nonneg_left (hb2 j) (le_of_lt hκpos)

theorem sum_inv_factorial_mul (j : ℕ) :
    (∑ m ∈ Finset.range (j + 1),
        (1:ℝ) / ((((j - m).factorial : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ)))
      = 2 ^ j / ((j.factorial : ℕ) : ℝ) := by
  have hfac : ((j.factorial : ℕ) : ℝ) ≠ 0 := by
    have := Nat.factorial_pos j
    positivity
  rw [eq_div_iff hfac, Finset.sum_mul]
  have hterm : ∀ m ∈ Finset.range (j + 1),
      (1:ℝ) / ((((j - m).factorial : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ))
        * ((j.factorial : ℕ) : ℝ) = ((j.choose m : ℕ) : ℝ) := by
    intro m hm
    have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hkey : ((j.choose m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ)
        * (((j - m).factorial : ℕ) : ℝ) = ((j.factorial : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul_factorial_mul_factorial hmj)
    have hm0 : ((m.factorial : ℕ) : ℝ) ≠ 0 := by
      have := Nat.factorial_pos m
      positivity
    have hjm0 : (((j - m).factorial : ℕ) : ℝ) ≠ 0 := by
      have := Nat.factorial_pos (j - m)
      positivity
    field_simp
    linarith [hkey]
  rw [Finset.sum_congr rfl hterm]
  have := Nat.sum_range_choose j
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this

/-- The Taylor image of the levels is bounded by `K Δ^j 2^j / j!`. -/
theorem norm_windowTaylor_le {a : ℕ → ℂ} {x y : ℝ} (hxy : x < y) {K : ℝ} {j : ℕ}
    (hstate : ∀ m ≤ j, ‖arithProfile a m x‖ ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K) :
    ‖windowTaylor a x y j‖ ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hDj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
  have hK0 : 0 ≤ K := by
    have h0 := hstate 0 (Nat.zero_le j)
    have hnn : 0 ≤ ‖arithProfile a 0 x‖ := norm_nonneg _
    by_contra hcon
    rw [not_le] at hcon
    have : ((y - x) ^ (0 : ℕ) / ((Nat.factorial 0 : ℕ) : ℝ)) * K < 0 := by
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      exact hcon
    linarith
  have hbound : ‖windowTaylor a x y j‖
      ≤ ∑ m ∈ Finset.range (j + 1),
          ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine le_trans hbound ?_
  have hterm : ∀ m ∈ Finset.range (j + 1),
      ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖
        ≤ K * (y - x) ^ j * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
    intro m hm
    have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hfacjm : (0:ℝ) < (((j - m).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (j - m)
    have hpow : (y - x) ^ (j - m) * (y - x) ^ m = (y - x) ^ j := by
      rw [← pow_add]
      congr 1
      omega
    calc ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖
        ≤ ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ))
            * (((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K) := by
          refine mul_le_mul_of_nonneg_left (hstate m hmj) ?_
          positivity
      _ = K * ((y - x) ^ (j - m) * (y - x) ^ m)
            * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
          field_simp
      _ = K * (y - x) ^ j
            * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
          rw [hpow]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : (∑ m ∈ Finset.range (j + 1),
      (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹))
      = 2 ^ j / ((j.factorial : ℕ) : ℝ) := by
    rw [← sum_inv_factorial_mul j]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [hsum]

/-- **The target stays bounded.**  If the levels at the base point obey the window bound with
constant `K`, the moment the next window must realize is at most `2^j K`. -/
theorem norm_windowTarget_le {a : ℕ → ℂ} {x y : ℝ} (hxy : x < y) {K : ℝ} {j : ℕ}
    (hstate : ∀ m ≤ j, ‖arithProfile a m x‖ ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K) :
    ‖windowTarget a x y j‖ ≤ 2 ^ j * K := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hDj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
  have hK0 : 0 ≤ K := by
    have h0 := hstate 0 (Nat.zero_le j)
    have hnn : 0 ≤ ‖arithProfile a 0 x‖ := norm_nonneg _
    by_contra hcon
    rw [not_le] at hcon
    have : ((y - x) ^ (0 : ℕ) / ((Nat.factorial 0 : ℕ) : ℝ)) * K < 0 := by
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      exact hcon
    linarith
  have htaylor : ‖windowTaylor a x y j‖ ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) :=
    norm_windowTaylor_le hxy hstate
  have hfinal : ‖windowTarget a x y j‖
      = (((j.factorial : ℕ) : ℝ) / (y - x) ^ j) * ‖windowTaylor a x y j‖ := by
    rw [windowTarget, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hfinal]
  calc (((j.factorial : ℕ) : ℝ) / (y - x) ^ j) * ‖windowTaylor a x y j‖
      ≤ (((j.factorial : ℕ) : ℝ) / (y - x) ^ j)
          * (K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left htaylor ?_
        positivity
    _ = 2 ^ j * K := by
        field_simp

/-- **The interior bound.**  Anywhere inside a window the level is controlled by the Taylor image of
the levels at the base point plus the mass of the window's own jumps. -/
theorem norm_arithProfile_window_le {a : ℕ → ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) {K M : ℝ}
    {j : ℕ}
    (hstate : ∀ m ≤ j, ‖arithProfile a m x‖ ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K)
    (hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖ ≤ M) :
    ‖arithProfile a j y‖ ≤ ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + M) := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hDj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
  have hy0 : (0:ℝ) ≤ y := by linarith
  rw [arithProfile_window a j hx (le_of_lt hxy)]
  refine le_trans (norm_add_le _ _) ?_
  have h2 : ‖windowTaylor a x y j‖ ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) :=
    norm_windowTaylor_le hxy hstate
  have h3 : ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
      ≤ ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
          ≤ ‖a n‖ * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) := by
      intro n hn
      have hmem := Finset.mem_Ioc.1 hn
      have hnx : x < (n : ℝ) := by
        have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmem.1
        have h2 := Nat.lt_floor_add_one x
        linarith
      have hny : (n : ℝ) ≤ y := by
        have h1 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
        exact le_trans h1 (Nat.floor_le hy0)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ))]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine div_le_div_of_nonneg_right ?_ hfac.le
      exact pow_le_pow_left₀ (by linarith) (by linarith) j
    calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖)
        ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖ * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖) * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
      _ ≤ M * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hmass ?_
          positivity
      _ = ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M := by ring
  have hcombine : K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
      = ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K) := by
    field_simp
  calc ‖windowTaylor a x y j‖
        + ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
      ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
        + ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M := add_le_add h2 h3
    _ = ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + M) := by
        rw [hcombine]
        ring

/-! ## Partial window updates

Only part of a window is ever free: the values already determined at prime powers must be kept.  The
decomposition and the moment problem therefore carry a *forced* term.
-/

/-- The contribution of the window's already-determined values. -/
def windowForced (a : ℕ → ℂ) (S : Finset ℕ) (x y : ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S,
    a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)

/-- **Window decomposition for a partial update.** -/
theorem arithProfile_updateWindow_partial (a c : ℕ → ℂ) {S : Finset ℕ} {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x ≤ y) (hS : S ⊆ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (j : ℕ) :
    arithProfile (updateWindow a S c) j y
      = windowTaylor a x y j + windowForced a S x y j
        + ∑ n ∈ S, c n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  classical
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hSx : ∀ n ∈ S, x < (n : ℝ) := by
    intro n hn
    have hmem := Finset.mem_Ioc.1 (hS hn)
    have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmem.1
    have h2 := Nat.lt_floor_add_one x
    linarith
  rw [arithProfile_window (updateWindow a S c) j hx hxy]
  have htaylor : (∑ m ∈ Finset.range (j + 1),
      (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
        * arithProfile (updateWindow a S c) m x) = windowTaylor a x y j := by
    rw [windowTaylor]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [arithProfile_updateWindow_base a c hx0 hSx m]
  rw [htaylor]
  have hsplit : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      updateWindow a S c n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ))
      = windowForced a S x y j
        + ∑ n ∈ S, c n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← Finset.sum_sdiff hS, windowForced]
    congr 1
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hnot : n ∉ S := (Finset.mem_sdiff.1 hn).2
      rw [updateWindow, if_neg hnot]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [updateWindow, if_pos hn]
  rw [hsplit, add_assoc]

/-- The moment vector a partially updated window must realize. -/
def windowTargetPartial (a : ℕ → ℂ) (S : Finset ℕ) (x y : ℝ) (j : ℕ) : ℂ :=
  -((((j.factorial : ℕ) : ℝ) / (y - x) ^ j : ℝ) : ℂ) * (windowTaylor a x y j + windowForced a S x y j)

theorem norm_windowForced_le {a : ℕ → ℂ} {S : Finset ℕ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y)
    {M : ℝ} (hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S, ‖a n‖ ≤ M) (j : ℕ) :
    ‖windowForced a S x y j‖ ≤ ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hy0 : (0:ℝ) ≤ y := by linarith
  rw [windowForced]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S,
      ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
        ≤ ‖a n‖ * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) := by
    intro n hn
    have hmem := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 hn).1
    have hnx : x < (n : ℝ) := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmem.1
      have h2 := Nat.lt_floor_add_one x
      linarith
    have hny : (n : ℝ) ≤ y := by
      have h1 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
      exact le_trans h1 (Nat.floor_le hy0)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine div_le_div_of_nonneg_right ?_ hfac.le
    exact pow_le_pow_left₀ (by linarith) (by linarith) j
  calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S,
          ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖)
      ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S, ‖a n‖ * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S, ‖a n‖) * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) := by
        rw [Finset.sum_mul]
    _ ≤ M * ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hmass ?_
        positivity
    _ = ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M := by ring

/-- **The partial target stays bounded.** -/
theorem norm_windowTargetPartial_le {a : ℕ → ℂ} {S : Finset ℕ} {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) {K M : ℝ} {j : ℕ}
    (hstate : ∀ m ≤ j, ‖arithProfile a m x‖ ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K)
    (hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S, ‖a n‖ ≤ M) :
    ‖windowTargetPartial a S x y j‖ ≤ 2 ^ j * K + M := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hDj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
  have h1 := norm_windowTaylor_le hxy hstate
  have h2 := norm_windowForced_le hx hxy hmass j
  have hsum : ‖windowTaylor a x y j + windowForced a S x y j‖
      ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
        + ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M := le_trans (norm_add_le _ _) (add_le_add h1 h2)
  rw [windowTargetPartial, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((j.factorial : ℕ) : ℝ) / (y - x) ^ j)]
  calc (((j.factorial : ℕ) : ℝ) / (y - x) ^ j) * ‖windowTaylor a x y j + windowForced a S x y j‖
      ≤ (((j.factorial : ℕ) : ℝ) / (y - x) ^ j)
          * (K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
            + ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        positivity
    _ = 2 ^ j * K + M := by
        field_simp

/-- **The window step with forced values.**  Assigning unimodular phases at the free nodes cancels
both the Taylor image of the old levels and the window's already-determined jumps, leaving only the
rounding error. -/
theorem exists_window_phases_partial {N J : ℕ} (hJ : 0 < J) (a : ℕ → ℂ) {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) {p : Fin N → ℕ} (hinj : Function.Injective p)
    (hp : ∀ r, p r ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (w : Fin N → ℝ) {C : ℝ} (hC : ∀ r, |w r| ≤ C)
    (hC0 : 0 ≤ C) {lam : ℝ} (hlam : 0 < lam)
    (hquad : ∀ u : Fin J → ℝ,
      lam * (∑ i, u i ^ (2 : ℕ)) ≤ u ⬝ᵥ (atomicHankel w (windowNode p x y) J).mulVec u)
    (hsize : (J : ℝ) * (∑ j : Fin J,
      ‖2 * windowTargetPartial a (Finset.image p Finset.univ) x y (j : ℕ)‖ ^ (2 : ℕ)) ≤ lam ^ (2 : ℕ)) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J,
        ‖arithProfile (updateWindow a (Finset.image p Finset.univ) (windowAssign p b w))
            (j : ℕ) y‖
          ≤ ((y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ)) * ((J : ℝ) * C) := by
  classical
  have hD : 0 < y - x := by linarith
  have hpS : ∀ r, p r ∈ Finset.image p Finset.univ := fun r =>
    Finset.mem_image.2 ⟨r, Finset.mem_univ r, rfl⟩
  have hS : Finset.image p Finset.univ ⊆ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    intro n hn
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hn
    exact hp r
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_window_moments_complex hJ hlam
    (windowNode p x y) w (windowNode_mem_Icc hx hxy hp) hC hC0 hquad
    (fun j => windowTargetPartial a (Finset.image p Finset.univ) x y (j : ℕ)) hsize
  refine ⟨b, hb1, fun j => ?_⟩
  have hfac : (0:ℝ) < (((j : ℕ).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j : ℕ)
  have hDj : (0:ℝ) < (y - x) ^ (j : ℕ) := pow_pos hD _
  set κ : ℝ := (y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) with hκ
  have hκpos : 0 < κ := by
    rw [hκ]
    exact div_pos hDj hfac
  have hstep := arithProfile_updateWindow_partial a (windowAssign p b w) hx (le_of_lt hxy) hS
    (j : ℕ)
  have hwindow : (∑ n ∈ Finset.image p Finset.univ, windowAssign p b w n
        * (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ))
      = (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ) := by
    rw [sum_windowAssign hinj b w hpS
      (fun n => (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hnode : (y - (p r : ℝ)) = (y - x) * windowNode p x y r := by
      rw [windowNode]
      field_simp
    rw [hnode, hκ, windowNode]
    push_cast
    rw [mul_pow]
    field_simp
  have hone : ((κ : ℝ) : ℂ)
      * (((((j : ℕ).factorial : ℕ) : ℝ) / (y - x) ^ (j : ℕ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hκ]
    norm_cast
    field_simp
  have htaylor : (κ : ℂ) * windowTargetPartial a (Finset.image p Finset.univ) x y (j : ℕ)
      = -(windowTaylor a x y (j : ℕ)
          + windowForced a (Finset.image p Finset.univ) x y (j : ℕ)) := by
    rw [windowTargetPartial, ← mul_assoc, mul_neg, hone, neg_one_mul]
  rw [hstep, hwindow]
  have hcollect : windowTaylor a x y (j : ℕ)
      + windowForced a (Finset.image p Finset.univ) x y (j : ℕ)
      + (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ)
      = (κ : ℂ) * ((∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ))
          - windowTargetPartial a (Finset.image p Finset.univ) x y (j : ℕ)) := by
    rw [mul_sub, htaylor]
    ring
  rw [hcollect, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
  exact mul_le_mul_of_nonneg_left (hb2 j) (le_of_lt hκpos)

/-- **The interior bound in a fixed scale.**  If the levels at the base point are measured in a
scale `S` at least as large as the distance travelled, the level at `y` obeys the same bound with
the window's own mass added. -/
theorem norm_arithProfile_window_le' {a : ℕ → ℂ} {x y S : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hS : y - x ≤ S) {K M : ℝ} {j : ℕ}
    (hstate : ∀ m ≤ j, ‖arithProfile a m x‖ ≤ (S ^ m / ((m.factorial : ℕ) : ℝ)) * K)
    (hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖ ≤ M) :
    ‖arithProfile a j y‖ ≤ (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + M) := by
  have hD : 0 ≤ y - x := by linarith
  have hS0 : 0 ≤ S := le_trans hD hS
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hy0 : (0:ℝ) ≤ y := by linarith
  rw [arithProfile_window a j hx hxy]
  refine le_trans (norm_add_le _ _) ?_
  -- the Taylor part
  have h1 : ‖windowTaylor a x y j‖ ≤ K * S ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) := by
    have hbound : ‖windowTaylor a x y j‖
        ≤ ∑ m ∈ Finset.range (j + 1),
            ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine le_trans hbound ?_
    have hterm : ∀ m ∈ Finset.range (j + 1),
        ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖
          ≤ K * S ^ j * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
      intro m hm
      have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hfacjm : (0:ℝ) < (((j - m).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (j - m)
      have hpowS : (y - x) ^ (j - m) ≤ S ^ (j - m) := pow_le_pow_left₀ hD hS (j - m)
      have hsplit : S ^ (j - m) * S ^ m = S ^ j := by
        rw [← pow_add]
        congr 1
        omega
      calc ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖
          ≤ (S ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ))
              * ((S ^ m / ((m.factorial : ℕ) : ℝ)) * K) := by
            refine mul_le_mul (div_le_div_of_nonneg_right hpowS hfacjm.le) (hstate m hmj)
              (norm_nonneg _) (by positivity)
        _ = K * (S ^ (j - m) * S ^ m)
              * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
            field_simp
        _ = K * S ^ j
              * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
            rw [hsplit]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsum : (∑ m ∈ Finset.range (j + 1),
        (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹))
        = 2 ^ j / ((j.factorial : ℕ) : ℝ) := by
      rw [← sum_inv_factorial_mul j]
      refine Finset.sum_congr rfl fun m _ => ?_
      field_simp
    rw [hsum]
  -- the window part
  have h2 : ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
      ≤ (S ^ j / ((j.factorial : ℕ) : ℝ)) * M := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
          ≤ ‖a n‖ * (S ^ j / ((j.factorial : ℕ) : ℝ)) := by
      intro n hn
      have hmem := Finset.mem_Ioc.1 hn
      have hnx : x < (n : ℝ) := by
        have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmem.1
        have h2 := Nat.lt_floor_add_one x
        linarith
      have hny : (n : ℝ) ≤ y := by
        have h1 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
        exact le_trans h1 (Nat.floor_le hy0)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ))]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine div_le_div_of_nonneg_right ?_ hfac.le
      exact pow_le_pow_left₀ (by linarith) (by linarith) j
    calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖)
        ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖ * (S ^ j / ((j.factorial : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖) * (S ^ j / ((j.factorial : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
      _ ≤ M * (S ^ j / ((j.factorial : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hmass ?_
          positivity
      _ = (S ^ j / ((j.factorial : ℕ) : ℝ)) * M := by ring
  have hcombine : K * S ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
      = (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K) := by
    field_simp
  calc ‖windowTaylor a x y j‖
        + ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
      ≤ K * S ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
        + (S ^ j / ((j.factorial : ℕ) : ℝ)) * M := add_le_add h1 h2
    _ = (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + M) := by
        rw [hcombine]
        ring

/-! ## The window step for the full remainder chain

The chain that Andersson's Theorem 1 uses is `∫_1^x q + ∑_{n ≤ x} a n` and its iterated integrals.
Its window decomposition is the arithmetic one plus the Taylor remainder of the datum, which is
itself an iterated antiderivative based at the window's left endpoint.
-/

/-- The Taylor image of the full levels. -/
def windowTaylorFull (q : ℝ → ℂ) (a : ℕ → ℂ) (x y : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (j + 1),
    (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * arithJumpProfile q a m x

/-- What the window cannot choose: the datum's Taylor remainder and the already-fixed jumps. -/
def windowForcedFull (q : ℝ → ℂ) (a : ℕ → ℂ) (S : Finset ℕ) (x y : ℝ) (j : ℕ) : ℂ :=
  iteratedAntiderivFrom q x (j + 1) y + windowForced a S x y j

/-- The moment the window must realize for the full chain. -/
def windowTargetFull (q : ℝ → ℂ) (a : ℕ → ℂ) (S : Finset ℕ) (x y : ℝ) (j : ℕ) : ℂ :=
  -((((j.factorial : ℕ) : ℝ) / (y - x) ^ j : ℝ) : ℂ)
    * (windowTaylorFull q a x y j + windowForcedFull q a S x y j)

/-- **Window decomposition of the full chain under a partial update.** -/
theorem arithJumpProfile_updateWindow_partial {q : ℝ → ℂ}
    (hq : ∀ u v : ℝ, IntervalIntegrable q volume u v) (a c : ℕ → ℂ) {S : Finset ℕ} {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hS : S ⊆ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (j : ℕ) :
    arithJumpProfile q (updateWindow a S c) j y
      = windowTaylorFull q a x y j + windowForcedFull q a S x y j
        + ∑ n ∈ S, c n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  classical
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hSx : ∀ n ∈ S, x < (n : ℝ) := by
    intro n hn
    have hmem := Finset.mem_Ioc.1 (hS hn)
    have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmem.1
    have h2 := Nat.lt_floor_add_one x
    linarith
  rw [arithJumpProfile_window hq (updateWindow a S c) j hx hxy]
  have htaylor : (∑ m ∈ Finset.range (j + 1),
      (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
        * arithJumpProfile q (updateWindow a S c) m x) = windowTaylorFull q a x y j := by
    rw [windowTaylorFull]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [arithJumpProfile_updateWindow_base a c hx0 hSx m]
  rw [htaylor]
  have hsplit : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      updateWindow a S c n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ))
      = windowForced a S x y j
        + ∑ n ∈ S, c n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← Finset.sum_sdiff hS, windowForced]
    congr 1
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hnot : n ∉ S := (Finset.mem_sdiff.1 hn).2
      rw [updateWindow, if_neg hnot]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [updateWindow, if_pos hn]
  rw [hsplit, windowForcedFull]
  ring

theorem norm_windowTaylorFull_le {q : ℝ → ℂ} {a : ℕ → ℂ} {x y : ℝ} (hxy : x < y) {K : ℝ} {j : ℕ}
    (hstate : ∀ m ≤ j, ‖arithJumpProfile q a m x‖
      ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K) :
    ‖windowTaylorFull q a x y j‖ ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hDj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
  have hK0 : 0 ≤ K := by
    have h0 := hstate 0 (Nat.zero_le j)
    have hnn : 0 ≤ ‖arithJumpProfile q a 0 x‖ := norm_nonneg _
    by_contra hcon
    rw [not_le] at hcon
    have : ((y - x) ^ (0 : ℕ) / ((Nat.factorial 0 : ℕ) : ℝ)) * K < 0 := by
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      exact hcon
    linarith
  have hbound : ‖windowTaylorFull q a x y j‖
      ≤ ∑ m ∈ Finset.range (j + 1),
          ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithJumpProfile q a m x‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine le_trans hbound ?_
  have hterm : ∀ m ∈ Finset.range (j + 1),
      ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithJumpProfile q a m x‖
        ≤ K * (y - x) ^ j * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
    intro m hm
    have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hfacjm : (0:ℝ) < (((j - m).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (j - m)
    have hpow : (y - x) ^ (j - m) * (y - x) ^ m = (y - x) ^ j := by
      rw [← pow_add]
      congr 1
      omega
    calc ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithJumpProfile q a m x‖
        ≤ ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ))
            * (((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K) := by
          refine mul_le_mul_of_nonneg_left (hstate m hmj) ?_
          positivity
      _ = K * ((y - x) ^ (j - m) * (y - x) ^ m)
            * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
          field_simp
      _ = K * (y - x) ^ j
            * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
          rw [hpow]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : (∑ m ∈ Finset.range (j + 1),
      (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹))
      = 2 ^ j / ((j.factorial : ℕ) : ℝ) := by
    rw [← sum_inv_factorial_mul j]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [hsum]

theorem norm_windowForcedFull_le {q : ℝ → ℂ} {a : ℕ → ℂ} {S : Finset ℕ} {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) {M Mq : ℝ} (hbound : ∀ t ∈ Set.Icc x y, ‖q t‖ ≤ Mq)
    (hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S, ‖a n‖ ≤ M) (j : ℕ) :
    ‖windowForcedFull q a S x y j‖
      ≤ ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (M + Mq * (y - x)) := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfacs : (0:ℝ) < (((j + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  have hMq : 0 ≤ Mq := le_trans (norm_nonneg _) (hbound x ⟨le_rfl, le_of_lt hxy⟩)
  have h1 : ‖iteratedAntiderivFrom q x (j + 1) y‖
      ≤ ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (Mq * (y - x)) := by
    refine le_trans (norm_iteratedAntiderivFrom_le hbound (le_of_lt hxy) (j + 1)) ?_
    have hfaceq : (((j + 1).factorial : ℕ) : ℝ) = ((j : ℝ) + 1) * ((j.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfaceq]
    have hj1 : (1:ℝ) ≤ (j : ℝ) + 1 := by
      have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hpow : (0:ℝ) < (y - x) ^ (j + 1) := pow_pos hD _
    rw [div_le_iff₀ (by positivity)]
    have hsplit : (y - x) ^ (j + 1) = (y - x) ^ j * (y - x) := by ring
    rw [hsplit]
    have hpowj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
    have hrw : (y - x) ^ j / ((j.factorial : ℕ) : ℝ) * (Mq * (y - x))
        * (((j:ℝ) + 1) * ((j.factorial : ℕ) : ℝ))
        = ((j:ℝ) + 1) * (Mq * ((y - x) ^ j * (y - x))) := by
      field_simp
    rw [hrw]
    have hT : 0 ≤ Mq * ((y - x) ^ j * (y - x)) :=
      mul_nonneg hMq (mul_nonneg hpowj.le hD.le)
    nlinarith [hj1, hT]
  have h2 := norm_windowForced_le hx hxy hmass j
  calc ‖windowForcedFull q a S x y j‖
      ≤ ‖iteratedAntiderivFrom q x (j + 1) y‖ + ‖windowForced a S x y j‖ := by
        rw [windowForcedFull]
        exact norm_add_le _ _
    _ ≤ ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (Mq * (y - x))
        + ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * M := add_le_add h1 h2
    _ = ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (M + Mq * (y - x)) := by ring

/-- **The full target stays bounded.** -/
theorem norm_windowTargetFull_le {q : ℝ → ℂ} {a : ℕ → ℂ} {S : Finset ℕ} {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) {K M Mq : ℝ} {j : ℕ} (hbound : ∀ t ∈ Set.Icc x y, ‖q t‖ ≤ Mq)
    (hstate : ∀ m ≤ j, ‖arithJumpProfile q a m x‖
      ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K)
    (hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ S, ‖a n‖ ≤ M) :
    ‖windowTargetFull q a S x y j‖ ≤ 2 ^ j * K + (M + Mq * (y - x)) := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hDj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
  have h1 := norm_windowTaylorFull_le hxy hstate
  have h2 := norm_windowForcedFull_le hx hxy hbound hmass j
  have hsum : ‖windowTaylorFull q a x y j + windowForcedFull q a S x y j‖
      ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
        + ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (M + Mq * (y - x)) :=
    le_trans (norm_add_le _ _) (add_le_add h1 h2)
  rw [windowTargetFull, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((j.factorial : ℕ) : ℝ) / (y - x) ^ j)]
  calc (((j.factorial : ℕ) : ℝ) / (y - x) ^ j)
        * ‖windowTaylorFull q a x y j + windowForcedFull q a S x y j‖
      ≤ (((j.factorial : ℕ) : ℝ) / (y - x) ^ j)
          * (K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
            + ((y - x) ^ j / ((j.factorial : ℕ) : ℝ)) * (M + Mq * (y - x))) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        positivity
    _ = 2 ^ j * K + (M + Mq * (y - x)) := by
        field_simp

/-- **The window step with forced values, for the full chain.**  Unimodular phases at the free
nodes cancel the Taylor image of the old full levels, the datum's Taylor remainder and the
window's already-determined jumps together. -/
theorem exists_window_phases_partial_full {N J : ℕ} (hJ : 0 < J) {q : ℝ → ℂ}
    (hq : ∀ u v : ℝ, IntervalIntegrable q volume u v) (a : ℕ → ℂ) {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) {p : Fin N → ℕ} (hinj : Function.Injective p)
    (hp : ∀ r, p r ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (w : Fin N → ℝ) {C : ℝ} (hC : ∀ r, |w r| ≤ C)
    (hC0 : 0 ≤ C) {lam : ℝ} (hlam : 0 < lam)
    (hquad : ∀ u : Fin J → ℝ,
      lam * (∑ i, u i ^ (2 : ℕ)) ≤ u ⬝ᵥ (atomicHankel w (windowNode p x y) J).mulVec u)
    (hsize : (J : ℝ) * (∑ j : Fin J,
      ‖2 * windowTargetFull q a (Finset.image p Finset.univ) x y (j : ℕ)‖ ^ (2 : ℕ)) ≤ lam ^ (2 : ℕ)) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J,
        ‖arithJumpProfile q (updateWindow a (Finset.image p Finset.univ) (windowAssign p b w))
            (j : ℕ) y‖
          ≤ ((y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ)) * ((J : ℝ) * C) := by
  classical
  have hD : 0 < y - x := by linarith
  have hpS : ∀ r, p r ∈ Finset.image p Finset.univ := fun r =>
    Finset.mem_image.2 ⟨r, Finset.mem_univ r, rfl⟩
  have hS : Finset.image p Finset.univ ⊆ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    intro n hn
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hn
    exact hp r
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_window_moments_complex hJ hlam
    (windowNode p x y) w (windowNode_mem_Icc hx hxy hp) hC hC0 hquad
    (fun j => windowTargetFull q a (Finset.image p Finset.univ) x y (j : ℕ)) hsize
  refine ⟨b, hb1, fun j => ?_⟩
  have hfac : (0:ℝ) < (((j : ℕ).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j : ℕ)
  have hDj : (0:ℝ) < (y - x) ^ (j : ℕ) := pow_pos hD _
  set κ : ℝ := (y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) with hκ
  have hκpos : 0 < κ := by
    rw [hκ]
    exact div_pos hDj hfac
  have hstep := arithJumpProfile_updateWindow_partial hq a (windowAssign p b w) hx (le_of_lt hxy)
    hS (j : ℕ)
  have hwindow : (∑ n ∈ Finset.image p Finset.univ, windowAssign p b w n
        * (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ))
      = (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ) := by
    rw [sum_windowAssign hinj b w hpS
      (fun n => (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hnode : (y - (p r : ℝ)) = (y - x) * windowNode p x y r := by
      rw [windowNode]
      field_simp
    rw [hnode, hκ, windowNode]
    push_cast
    rw [mul_pow]
    field_simp
  have hone : ((κ : ℝ) : ℂ)
      * (((((j : ℕ).factorial : ℕ) : ℝ) / (y - x) ^ (j : ℕ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hκ]
    norm_cast
    field_simp
  have htaylor : (κ : ℂ) * windowTargetFull q a (Finset.image p Finset.univ) x y (j : ℕ)
      = -(windowTaylorFull q a x y (j : ℕ)
          + windowForcedFull q a (Finset.image p Finset.univ) x y (j : ℕ)) := by
    rw [windowTargetFull, ← mul_assoc, mul_neg, hone, neg_one_mul]
  rw [hstep, hwindow]
  have hcollect : windowTaylorFull q a x y (j : ℕ)
      + windowForcedFull q a (Finset.image p Finset.univ) x y (j : ℕ)
      + (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ)
      = (κ : ℂ) * ((∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ))
          - windowTargetFull q a (Finset.image p Finset.univ) x y (j : ℕ)) := by
    rw [mul_sub, htaylor]
    ring
  rw [hcollect, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
  exact mul_le_mul_of_nonneg_left (hb2 j) (le_of_lt hκpos)

/-- The Taylor image of a family of levels measured in a scale `S` at least as large as the
distance travelled. -/
theorem norm_taylorLevels_le {v : ℕ → ℂ} {x y S K : ℝ} (hD : 0 ≤ y - x) (hS : y - x ≤ S) {j : ℕ}
    (hstate : ∀ m ≤ j, ‖v m‖ ≤ (S ^ m / ((m.factorial : ℕ) : ℝ)) * K) :
    ‖∑ m ∈ Finset.range (j + 1),
        (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * v m‖
      ≤ K * S ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) := by
  have hS0 : 0 ≤ S := le_trans hD hS
  have hbound : ‖∑ m ∈ Finset.range (j + 1),
      (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * v m‖
      ≤ ∑ m ∈ Finset.range (j + 1),
          ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖v m‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine le_trans hbound ?_
  have hterm : ∀ m ∈ Finset.range (j + 1),
      ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖v m‖
        ≤ K * S ^ j * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
    intro m hm
    have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hfacjm : (0:ℝ) < (((j - m).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (j - m)
    have hpowS : (y - x) ^ (j - m) ≤ S ^ (j - m) := pow_le_pow_left₀ hD hS (j - m)
    have hsplit : S ^ (j - m) * S ^ m = S ^ j := by
      rw [← pow_add]
      congr 1
      omega
    calc ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖v m‖
        ≤ (S ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ))
            * ((S ^ m / ((m.factorial : ℕ) : ℝ)) * K) := by
          refine mul_le_mul (div_le_div_of_nonneg_right hpowS hfacjm.le) (hstate m hmj)
            (norm_nonneg _) (div_nonneg (pow_nonneg hS0 _) hfacjm.le)
      _ = K * (S ^ (j - m) * S ^ m)
            * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
          field_simp
      _ = K * S ^ j
            * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
          rw [hsplit]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : (∑ m ∈ Finset.range (j + 1),
      (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹))
      = 2 ^ j / ((j.factorial : ℕ) : ℝ) := by
    rw [← sum_inv_factorial_mul j]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [hsum]

/-- **The interior bound for the full chain in a fixed scale.** -/
theorem norm_arithJumpProfile_window_le' {q : ℝ → ℂ}
    (hq : ∀ u v : ℝ, IntervalIntegrable q volume u v) {a : ℕ → ℂ} {x y S : ℝ} (hx : 1 ≤ x)
    (hxy : x ≤ y) (hSge : y - x ≤ S) {K M Mq : ℝ} {j : ℕ}
    (hbound : ∀ t ∈ Set.Icc x y, ‖q t‖ ≤ Mq)
    (hstate : ∀ m ≤ j, ‖arithJumpProfile q a m x‖ ≤ (S ^ m / ((m.factorial : ℕ) : ℝ)) * K)
    (hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖ ≤ M) :
    ‖arithJumpProfile q a j y‖
      ≤ (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + M + Mq * S) := by
  have hD : 0 ≤ y - x := by linarith
  have hS0 : 0 ≤ S := le_trans hD hSge
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfacs : (0:ℝ) < (((j + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  have hMq : 0 ≤ Mq := le_trans (norm_nonneg _) (hbound x ⟨le_rfl, hxy⟩)
  have hy0 : (0:ℝ) ≤ y := by linarith
  rw [arithJumpProfile_window hq a j hx hxy]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  -- the Taylor part
  have h1 : ‖∑ m ∈ Finset.range (j + 1),
      (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * arithJumpProfile q a m x‖
      ≤ K * S ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) :=
    norm_taylorLevels_le hD hSge hstate
  -- the Taylor remainder of the datum
  have h3 : ‖iteratedAntiderivFrom q x (j + 1) y‖
      ≤ (S ^ j / ((j.factorial : ℕ) : ℝ)) * (Mq * S) := by
    refine le_trans (norm_iteratedAntiderivFrom_le hbound hxy (j + 1)) ?_
    have hpowle : (y - x) ^ (j + 1) ≤ S ^ (j + 1) := pow_le_pow_left₀ hD hSge _
    have hfacle : ((j.factorial : ℕ) : ℝ) ≤ (((j + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ j)
    have hR : (S ^ j / ((j.factorial : ℕ) : ℝ)) * (Mq * S)
        = Mq * S ^ (j + 1) / ((j.factorial : ℕ) : ℝ) := by
      field_simp
      ring
    rw [hR, div_le_div_iff₀ hfacs hfac]
    have step1 : Mq * (y - x) ^ (j + 1) ≤ Mq * S ^ (j + 1) :=
      mul_le_mul_of_nonneg_left hpowle hMq
    have hB : 0 ≤ Mq * S ^ (j + 1) := by positivity
    have e1 : Mq * (y - x) ^ (j + 1) * ((j.factorial : ℕ) : ℝ)
        ≤ Mq * S ^ (j + 1) * ((j.factorial : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right step1 hfac.le
    have e2 : Mq * S ^ (j + 1) * ((j.factorial : ℕ) : ℝ)
        ≤ Mq * S ^ (j + 1) * (((j + 1).factorial : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hfacle hB
    linarith
  -- the window part
  have h2 : ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
      ≤ (S ^ j / ((j.factorial : ℕ) : ℝ)) * M := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
          ≤ ‖a n‖ * (S ^ j / ((j.factorial : ℕ) : ℝ)) := by
      intro n hn
      have hmem := Finset.mem_Ioc.1 hn
      have hnx : x < (n : ℝ) := by
        have hb1 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmem.1
        have hb2 := Nat.lt_floor_add_one x
        linarith
      have hny : (n : ℝ) ≤ y := by
        have hb1 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
        exact le_trans hb1 (Nat.floor_le hy0)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ))]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine div_le_div_of_nonneg_right ?_ hfac.le
      refine le_trans (pow_le_pow_left₀ (by linarith) (by linarith : y - (n:ℝ) ≤ y - x) j) ?_
      exact pow_le_pow_left₀ hD hSge j
    calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            ‖a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖)
        ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖ * (S ^ j / ((j.factorial : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖) * (S ^ j / ((j.factorial : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
      _ ≤ M * (S ^ j / ((j.factorial : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hmass ?_
          positivity
      _ = (S ^ j / ((j.factorial : ℕ) : ℝ)) * M := by ring
  have hcombine : K * S ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
      = (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K) := by
    field_simp
  calc ‖∑ m ∈ Finset.range (j + 1),
          (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
            * arithJumpProfile q a m x‖
        + ‖iteratedAntiderivFrom q x (j + 1) y‖
        + ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ)‖
      ≤ K * S ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))
        + (S ^ j / ((j.factorial : ℕ) : ℝ)) * (Mq * S)
        + (S ^ j / ((j.factorial : ℕ) : ℝ)) * M := add_le_add (add_le_add h1 h3) h2
    _ = (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + M + Mq * S) := by
        rw [hcombine]
        ring

end GaloisForLFunctions.HTGeometry

end
