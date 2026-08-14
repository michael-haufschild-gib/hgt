import GaloisForLFunctions.HTGeometry.PointSupportPrincipalOperator
import GaloisForLFunctions.HTGeometry.TemperedOrder

/-!
# Coordinate powers of a compactly supported test function

For a test function supported in a fixed bounded interval, multiplication by the coordinate raises
each Schwartz seminorm by a factor controlled by the interval and the differentiation order:

`‖·‖^k ‖D^l (x φ)‖ ≤ B ‖·‖^k ‖D^l φ‖ + l ‖·‖^k ‖D^{l-1} φ‖`.

Iterating, the block of seminorms with `k ≤ K` and `l ≤ L` grows at most like `(B+L)^n` along the
coordinate powers `x^n φ`.  Since a tempered distribution is bounded by finitely many seminorms, its
values along coordinate powers grow at most geometrically.  This is the estimate that makes the
exponential twist of a vector-valued tempered distribution by a bounded operator converge.
-/

open Set SchwartzMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Iterated multiplication by the coordinate on Schwartz space. -/
def coordPow : ℕ → (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
  | 0 => ContinuousLinearMap.id ℂ (SchwartzMap ℝ ℂ)
  | (n + 1) => coordMulCLM.comp (coordPow n)

@[simp] theorem coordPow_zero (φ : SchwartzMap ℝ ℂ) : coordPow 0 φ = φ := rfl

theorem coordPow_succ (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    coordPow (n + 1) φ = coordMulCLM (coordPow n φ) := rfl

theorem coordPow_apply (n : ℕ) (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ((coordPow n φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = (φ : ℝ → ℂ) x * (x : ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [coordPow_succ, coordMulCLM_apply, ih, pow_succ, mul_assoc]

/-- Coordinate powers preserve the carrier of a test function. -/
theorem coordPow_eq_zero_of_notMem {φ : SchwartzMap ℝ ℂ} {a b : ℝ}
    (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) (n : ℕ) :
    ∀ x, x ∉ Ioo a b → ((coordPow n φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := by
  intro x hx
  rw [coordPow_apply, hsupp x hx, zero_mul]

/-- Outside the closed interval carrying a test function every iterated derivative vanishes. -/
theorem iteratedDeriv_eq_zero_of_notMem_Icc {ψ : SchwartzMap ℝ ℂ} {a b : ℝ}
    (hsupp : ∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0) (n : ℕ) {x : ℝ} (hx : x ∉ Icc a b) :
    iteratedDeriv n (ψ : ℝ → ℂ) x = 0 := by
  have hopen : IsOpen ((Icc a b)ᶜ) := isClosed_Icc.isOpen_compl
  have heq : (ψ : ℝ → ℂ) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hsupp y fun hcon => hy ⟨hcon.1.le, hcon.2.le⟩
  have h := (Filter.EventuallyEq.iteratedFDeriv ℝ heq n).self_of_nhds
  rw [iteratedDeriv, h]
  simp

/-- Points of a bounded interval are bounded by the larger endpoint modulus. -/
theorem abs_le_max_abs_of_mem_Icc {a b x : ℝ} (hx : x ∈ Icc a b) : |x| ≤ max |a| |b| := by
  rcases le_or_gt 0 x with hpos | hneg
  · refine le_trans ?_ (le_max_right |a| |b|)
    rw [abs_of_nonneg hpos]
    exact le_trans hx.2 (le_abs_self b)
  · refine le_trans ?_ (le_max_left |a| |b|)
    rw [abs_of_neg hneg]
    have : -x ≤ -a := neg_le_neg hx.1
    exact le_trans this (neg_le_abs a)

/-- Multiplication by the coordinate raises one Schwartz seminorm of a compactly supported test
function by the interval bound plus the differentiation order. -/
theorem seminorm_coordMulCLM_le {ψ : SchwartzMap ℝ ℂ} {a b B : ℝ}
    (hsupp : ∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0)
    (hB : 0 ≤ B) (hle : ∀ x ∈ Icc a b, |x| ≤ B) (k l : ℕ) :
    SchwartzMap.seminorm ℂ k l (coordMulCLM ψ)
      ≤ B * SchwartzMap.seminorm ℂ k l ψ + (l : ℝ) * SchwartzMap.seminorm ℂ k (l - 1) ψ := by
  have hnn : (0 : ℝ) ≤ B * SchwartzMap.seminorm ℂ k l ψ
      + (l : ℝ) * SchwartzMap.seminorm ℂ k (l - 1) ψ :=
    add_nonneg (mul_nonneg hB (apply_nonneg _ _))
      (mul_nonneg (Nat.cast_nonneg l) (apply_nonneg _ _))
  refine SchwartzMap.seminorm_le_bound' ℂ k l _ hnn fun x => ?_
  by_cases hx : x ∈ Icc a b
  · have hcoe : ((coordMulCLM ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        = fun y : ℝ => (ψ : ℝ → ℂ) y * (y : ℂ) := rfl
    have hsm : ContDiff ℝ (⊤ : ℕ∞) ((ψ : ℝ → ℂ)) := ψ.smooth'
    rw [hcoe, iteratedDeriv_mul_coord hsm l x]
    have hxB : |x| ≤ B := hle x hx
    have hsem : ∀ m : ℕ, |x| ^ k * ‖iteratedDeriv m (ψ : ℝ → ℂ) x‖
        ≤ SchwartzMap.seminorm ℂ k m ψ := by
      intro m
      have h := SchwartzMap.le_seminorm ℂ k m ψ x
      rwa [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
    have htri : ‖iteratedDeriv l (ψ : ℝ → ℂ) x * (x : ℂ)
        + (l : ℂ) * iteratedDeriv (l - 1) (ψ : ℝ → ℂ) x‖
        ≤ ‖iteratedDeriv l (ψ : ℝ → ℂ) x‖ * |x|
          + (l : ℝ) * ‖iteratedDeriv (l - 1) (ψ : ℝ → ℂ) x‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    have hxk : (0 : ℝ) ≤ |x| ^ k := by positivity
    calc |x| ^ k * ‖iteratedDeriv l (ψ : ℝ → ℂ) x * (x : ℂ)
            + (l : ℂ) * iteratedDeriv (l - 1) (ψ : ℝ → ℂ) x‖
        ≤ |x| ^ k * (‖iteratedDeriv l (ψ : ℝ → ℂ) x‖ * |x|
            + (l : ℝ) * ‖iteratedDeriv (l - 1) (ψ : ℝ → ℂ) x‖) :=
          mul_le_mul_of_nonneg_left htri hxk
      _ = (|x| ^ k * ‖iteratedDeriv l (ψ : ℝ → ℂ) x‖) * |x|
            + (l : ℝ) * (|x| ^ k * ‖iteratedDeriv (l - 1) (ψ : ℝ → ℂ) x‖) := by ring
      _ ≤ (|x| ^ k * ‖iteratedDeriv l (ψ : ℝ → ℂ) x‖) * B
            + (l : ℝ) * SchwartzMap.seminorm ℂ k (l - 1) ψ := by
          refine add_le_add (mul_le_mul_of_nonneg_left hxB (by positivity)) ?_
          exact mul_le_mul_of_nonneg_left (hsem (l - 1)) (Nat.cast_nonneg l)
      _ ≤ B * SchwartzMap.seminorm ℂ k l ψ
            + (l : ℝ) * SchwartzMap.seminorm ℂ k (l - 1) ψ := by
          refine add_le_add ?_ le_rfl
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hsem l) hB
  · have hzero : iteratedDeriv l ((coordMulCLM ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := by
      refine iteratedDeriv_eq_zero_of_notMem_Icc (a := a) (b := b) ?_ l hx
      intro y hy
      rw [coordMulCLM_apply, hsupp y hy, zero_mul]
    rw [hzero]
    simpa using hnn

/-- The square block of Schwartz seminorms with orders at most `K` and `L`. -/
def blockSeminorm (K L : ℕ) : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
  ((Finset.range (K + 1)) ×ˢ (Finset.range (L + 1))).sup (schwartzSeminormFamily ℂ ℝ ℂ)

theorem seminorm_le_blockSeminorm {K L k l : ℕ} (hk : k ≤ K) (hl : l ≤ L)
    (φ : SchwartzMap ℝ ℂ) :
    SchwartzMap.seminorm ℂ k l φ ≤ blockSeminorm K L φ := by
  have hmem : (k, l) ∈ (Finset.range (K + 1)) ×ˢ (Finset.range (L + 1)) := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have h : schwartzSeminormFamily ℂ ℝ ℂ (k, l)
      ≤ ((Finset.range (K + 1)) ×ˢ (Finset.range (L + 1))).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.le_sup hmem
  exact Seminorm.le_def.mp h φ

/-- Multiplication by the coordinate expands the seminorm block of a compactly supported test
function by at most `B + L`. -/
theorem blockSeminorm_coordMulCLM_le {ψ : SchwartzMap ℝ ℂ} {a b B : ℝ} {K L : ℕ}
    (hsupp : ∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0)
    (hB : 0 ≤ B) (hle : ∀ x ∈ Icc a b, |x| ≤ B) :
    blockSeminorm K L (coordMulCLM ψ) ≤ (B + (L : ℝ)) * blockSeminorm K L ψ := by
  have hblk : (0 : ℝ) ≤ blockSeminorm K L ψ := apply_nonneg _ _
  refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range] at hp
  have hk : p.1 ≤ K := by omega
  have hl : p.2 ≤ L := by omega
  have hstep := seminorm_coordMulCLM_le hsupp hB hle p.1 p.2
  have h1 : SchwartzMap.seminorm ℂ p.1 p.2 ψ ≤ blockSeminorm K L ψ :=
    seminorm_le_blockSeminorm hk hl ψ
  have h2 : SchwartzMap.seminorm ℂ p.1 (p.2 - 1) ψ ≤ blockSeminorm K L ψ :=
    seminorm_le_blockSeminorm hk (le_trans (Nat.sub_le _ _) hl) ψ
  have hp2 : (p.2 : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr hl
  have hfam : schwartzSeminormFamily ℂ ℝ ℂ p (coordMulCLM ψ)
      = SchwartzMap.seminorm ℂ p.1 p.2 (coordMulCLM ψ) := rfl
  rw [hfam]
  calc SchwartzMap.seminorm ℂ p.1 p.2 (coordMulCLM ψ)
      ≤ B * SchwartzMap.seminorm ℂ p.1 p.2 ψ
        + (p.2 : ℝ) * SchwartzMap.seminorm ℂ p.1 (p.2 - 1) ψ := hstep
    _ ≤ B * blockSeminorm K L ψ + (L : ℝ) * blockSeminorm K L ψ := by
        refine add_le_add (mul_le_mul_of_nonneg_left h1 hB) ?_
        exact mul_le_mul hp2 h2 (apply_nonneg _ _) (Nat.cast_nonneg L)
    _ = (B + (L : ℝ)) * blockSeminorm K L ψ := by ring

/-- The seminorm block along coordinate powers grows at most geometrically. -/
theorem blockSeminorm_coordPow_le {φ : SchwartzMap ℝ ℂ} {a b B : ℝ} {K L : ℕ}
    (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0)
    (hB : 0 ≤ B) (hle : ∀ x ∈ Icc a b, |x| ≤ B) (n : ℕ) :
    blockSeminorm K L (coordPow n φ) ≤ (B + (L : ℝ)) ^ n * blockSeminorm K L φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := blockSeminorm_coordMulCLM_le (K := K) (L := L)
      (coordPow_eq_zero_of_notMem hsupp n) hB hle
    have hpos : (0 : ℝ) ≤ B + (L : ℝ) := by positivity
    rw [coordPow_succ]
    calc blockSeminorm K L (coordMulCLM (coordPow n φ))
        ≤ (B + (L : ℝ)) * blockSeminorm K L (coordPow n φ) := hstep
      _ ≤ (B + (L : ℝ)) * ((B + (L : ℝ)) ^ n * blockSeminorm K L φ) :=
          mul_le_mul_of_nonneg_left ih hpos
      _ = (B + (L : ℝ)) ^ (n + 1) * blockSeminorm K L φ := by ring

/-- **A tempered distribution grows at most geometrically along coordinate powers of a compactly
supported test function.** -/
theorem exists_bound_coordPow (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ}
    {φ : SchwartzMap ℝ ℂ} (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ n : ℕ, ‖u (coordPow n φ)‖ ≤ C * D ^ n := by
  obtain ⟨s, C₀, hC₀, hbound⟩ := exists_schwartz_seminorm_bound u
  set K : ℕ := s.sup (fun p : ℕ × ℕ => p.1) with hK
  set L : ℕ := s.sup (fun p : ℕ × ℕ => p.2) with hL
  set B : ℝ := max |a| |b| with hBdef
  have hB : 0 ≤ B := le_trans (abs_nonneg a) (le_max_left _ _)
  have hle : ∀ x ∈ Icc a b, |x| ≤ B := fun x hx => abs_le_max_abs_of_mem_Icc hx
  have hsub : s ⊆ (Finset.range (K + 1)) ×ˢ (Finset.range (L + 1)) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by have := Finset.le_sup (f := fun q : ℕ × ℕ => q.1) hp; omega,
      by have := Finset.le_sup (f := fun q : ℕ × ℕ => q.2) hp; omega⟩
  have hsupsub : ∀ ψ : SchwartzMap ℝ ℂ,
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψ ≤ blockSeminorm K L ψ := by
    intro ψ
    exact Seminorm.le_def.mp (Finset.sup_mono hsub) ψ
  refine ⟨C₀ * blockSeminorm K L φ, B + (L : ℝ), by positivity, by positivity, fun n => ?_⟩
  calc ‖u (coordPow n φ)‖
      ≤ C₀ * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (coordPow n φ) := hbound _
    _ ≤ C₀ * blockSeminorm K L (coordPow n φ) :=
        mul_le_mul_of_nonneg_left (hsupsub _) hC₀.le
    _ ≤ C₀ * ((B + (L : ℝ)) ^ n * blockSeminorm K L φ) :=
        mul_le_mul_of_nonneg_left (blockSeminorm_coordPow_le hsupp hB hle n) hC₀.le
    _ = (C₀ * blockSeminorm K L φ) * (B + (L : ℝ)) ^ n := by ring

end

end GaloisForLFunctions.HTGeometry
