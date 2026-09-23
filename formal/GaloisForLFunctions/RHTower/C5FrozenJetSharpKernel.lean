import GaloisForLFunctions.RHTower.C5FrozenJetGrowthBound

/-!
# Sharp kernel constants for the frozen-jet growth bound

`|K₁| ≤ S₅ t⁶/90` and `|K₂| ≤ S₄ t⁵/15`, by a one-sided comparison with the extremal profiles
`S s⁵/120` and `S s⁴/24`, through a chain of four (resp. three) monotonicity steps.
-/

namespace RHTower

open Set

/-- `h 0 = 0` and `h' ≥ 0` on `[0,t]` give `h ≥ 0` on `[0,t]`. -/
theorem nonneg_of_deriv_nonneg_Icc {h h' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (h0 : h 0 = 0)
    (hd : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt h (h' s) s) (hb : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ h' s) :
    ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ h s := by
  have hmono : MonotoneOn h (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · intro s hs
      exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact hb s (interior_subset hs)
  intro s hs
  have := hmono ⟨le_rfl, ht⟩ hs hs.1
  linarith

/-- `h 0 = 0` and `|h'| ≤ S` on `[0,t]` give `|h s| ≤ S s`. -/
theorem abs_le_mul_of_abs_deriv_le {h h' : ℝ → ℝ} {S t : ℝ} (ht : 0 ≤ t) (h0 : h 0 = 0)
    (hd : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt h (h' s) s) (hb : ∀ s ∈ Icc (0 : ℝ) t, |h' s| ≤ S) :
    ∀ s ∈ Icc (0 : ℝ) t, |h s| ≤ S * s := by
  have := abs_le_pow_div_of_abs_deriv_le (k := 0) ht h0 hd (fun s hs => by simpa using hb s hs)
  intro s hs
  have := this s hs
  simpa using this

/-- **One-sided sharp bound for the odd kernel.** -/
theorem kernelOne_le {o o₁ o₂ o₃ o₄ o₅ O : ℝ → ℝ} {S t : ℝ} (ht : 0 ≤ t)
    (hO : ∀ s, HasDerivAt O (o s) s) (ho : ∀ s, HasDerivAt o (o₁ s) s)
    (ho₁ : ∀ s, HasDerivAt o₁ (o₂ s) s) (ho₂ : ∀ s, HasDerivAt o₂ (o₃ s) s)
    (ho₃ : ∀ s, HasDerivAt o₃ (o₄ s) s) (ho₄ : ∀ s, HasDerivAt o₄ (o₅ s) s)
    (hO0 : O 0 = 0) (ho0 : o 0 = 0) (ho₂0 : o₂ 0 = 0) (ho₄0 : o₄ 0 = 0)
    (hS : ∀ s ∈ Icc (0 : ℝ) t, |o₅ s| ≤ S) :
    t ^ (2 : ℕ) * o₁ t - 5 * t * o t + 8 * O t ≤ S * t ^ (6 : ℕ) / 90 := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0 ⟨le_rfl, ht⟩)
  have h4 : ∀ s ∈ Icc (0 : ℝ) t, |o₄ s| ≤ S * s :=
    abs_le_mul_of_abs_deriv_le ht ho₄0 (fun s _ => ho₄ s) hS
  -- level 3
  have hG₃ : ∀ s ∈ Icc (0 : ℝ) t,
      0 ≤ 4 / 3 * S * s ^ (3 : ℕ) - (s ^ (2 : ℕ) * o₄ s + s * o₃ s - o₂ s) := by
    refine nonneg_of_deriv_nonneg_Icc (h' := fun s => 4 * S * s ^ (2 : ℕ) - (s ^ (2 : ℕ) * o₅ s + 3 * s * o₄ s))
      ht (by simp [ho₂0]) (fun s _ => ?_) (fun s hs => ?_)
    · have := ((hasDerivAt_pow 3 s).const_mul (4 / 3 * S)).sub
        ((((hasDerivAt_pow 2 s).mul (ho₄ s)).add ((hasDerivAt_id s).mul (ho₃ s))).sub (ho₂ s))
      exact this.congr_deriv (by
        simp only [id_eq]; push_cast
        ring)
    · have h5 := (abs_le.mp (hS s hs)).2
      have h4' := (abs_le.mp (h4 s hs)).2
      have hs2 : 0 ≤ s ^ (2 : ℕ) := by positivity
      have := mul_le_mul_of_nonneg_left h5 hs2
      have := mul_le_mul_of_nonneg_left h4' hs.1
      nlinarith
  -- level 2
  have hG₂ : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ S * s ^ (4 : ℕ) / 3 - (s ^ (2 : ℕ) * o₃ s - s * o₂ s) := by
    refine nonneg_of_deriv_nonneg_Icc
      (h' := fun s => 4 / 3 * S * s ^ (3 : ℕ) - (s ^ (2 : ℕ) * o₄ s + s * o₃ s - o₂ s)) ht (by simp)
      (fun s _ => ?_) hG₃
    have := (((hasDerivAt_pow 4 s).const_mul S).div_const 3).sub
      (((hasDerivAt_pow 2 s).mul (ho₃ s)).sub ((hasDerivAt_id s).mul (ho₂ s)))
    exact this.congr_deriv (by simp only [id_eq]; push_cast; ring)
  -- level 1
  have hG₁ : ∀ s ∈ Icc (0 : ℝ) t,
      0 ≤ S * s ^ (5 : ℕ) / 15 - (s ^ (2 : ℕ) * o₂ s - 3 * s * o₁ s + 3 * o s) := by
    refine nonneg_of_deriv_nonneg_Icc
      (h' := fun s => S * s ^ (4 : ℕ) / 3 - (s ^ (2 : ℕ) * o₃ s - s * o₂ s)) ht (by simp [ho0])
      (fun s _ => ?_) hG₂
    have := (((hasDerivAt_pow 5 s).const_mul S).div_const 15).sub
      ((((hasDerivAt_pow 2 s).mul (ho₂ s)).sub (((hasDerivAt_id s).const_mul (3 : ℝ)).mul (ho₁ s))).add
        ((ho s).const_mul (3 : ℝ)))
    exact this.congr_deriv (by simp only [id_eq]; push_cast; ring)
  -- level 0
  have hG₀ : ∀ s ∈ Icc (0 : ℝ) t,
      0 ≤ S * s ^ (6 : ℕ) / 90 - (s ^ (2 : ℕ) * o₁ s - 5 * s * o s + 8 * O s) := by
    refine nonneg_of_deriv_nonneg_Icc
      (h' := fun s => S * s ^ (5 : ℕ) / 15 - (s ^ (2 : ℕ) * o₂ s - 3 * s * o₁ s + 3 * o s)) ht (by simp [hO0])
      (fun s _ => ?_) hG₁
    have := (((hasDerivAt_pow 6 s).const_mul S).div_const 90).sub
      ((((hasDerivAt_pow 2 s).mul (ho₁ s)).sub (((hasDerivAt_id s).const_mul (5 : ℝ)).mul (ho s))).add
        ((hO s).const_mul (8 : ℝ)))
    exact this.congr_deriv (by simp only [id_eq]; push_cast; ring)
  have := hG₀ t ⟨ht, le_rfl⟩
  linarith

/-- **Sharp bound for the odd kernel** `|t²o₁ − 5to + 8O| ≤ S t⁶/90`. -/
theorem abs_kernelOne_le {o o₁ o₂ o₃ o₄ o₅ O : ℝ → ℝ} {S t : ℝ} (ht : 0 ≤ t)
    (hO : ∀ s, HasDerivAt O (o s) s) (ho : ∀ s, HasDerivAt o (o₁ s) s)
    (ho₁ : ∀ s, HasDerivAt o₁ (o₂ s) s) (ho₂ : ∀ s, HasDerivAt o₂ (o₃ s) s)
    (ho₃ : ∀ s, HasDerivAt o₃ (o₄ s) s) (ho₄ : ∀ s, HasDerivAt o₄ (o₅ s) s)
    (hO0 : O 0 = 0) (ho0 : o 0 = 0) (ho₂0 : o₂ 0 = 0) (ho₄0 : o₄ 0 = 0)
    (hS : ∀ s ∈ Icc (0 : ℝ) t, |o₅ s| ≤ S) :
    |t ^ (2 : ℕ) * o₁ t - 5 * t * o t + 8 * O t| ≤ S * t ^ (6 : ℕ) / 90 := by
  have hup := kernelOne_le ht hO ho ho₁ ho₂ ho₃ ho₄ hO0 ho0 ho₂0 ho₄0 hS
  have hlow := kernelOne_le (o := fun s => -o s) (o₁ := fun s => -o₁ s) (o₂ := fun s => -o₂ s)
    (o₃ := fun s => -o₃ s) (o₄ := fun s => -o₄ s) (o₅ := fun s => -o₅ s) (O := fun s => -O s) ht
    (fun s => (hO s).neg) (fun s => (ho s).neg) (fun s => (ho₁ s).neg) (fun s => (ho₂ s).neg)
    (fun s => (ho₃ s).neg) (fun s => (ho₄ s).neg) (by simp [hO0]) (by simp [ho0]) (by simp [ho₂0])
    (by simp [ho₄0]) (fun s hs => by simpa using hS s hs)
  rw [abs_le]
  constructor <;> linarith

/-- **One-sided sharp bound for the even kernel.** -/
theorem kernelTwo_ge {e e₁ e₂ e₃ e₄ E : ℝ → ℝ} {S t : ℝ} (ht : 0 ≤ t)
    (hE : ∀ s, HasDerivAt E (e s) s) (he : ∀ s, HasDerivAt e (e₁ s) s)
    (he₁ : ∀ s, HasDerivAt e₁ (e₂ s) s) (he₂ : ∀ s, HasDerivAt e₂ (e₃ s) s)
    (he₃ : ∀ s, HasDerivAt e₃ (e₄ s) s)
    (hE0 : E 0 = 0) (he₁0 : e₁ 0 = 0) (he₃0 : e₃ 0 = 0)
    (hS : ∀ s ∈ Icc (0 : ℝ) t, |e₄ s| ≤ S) :
    -(S * t ^ (5 : ℕ) / 15) ≤ 3 * t * e t - 3 * E t - t ^ (2 : ℕ) * e₁ t := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0 ⟨le_rfl, ht⟩)
  have h3 : ∀ s ∈ Icc (0 : ℝ) t, |e₃ s| ≤ S * s :=
    abs_le_mul_of_abs_deriv_le ht he₃0 (fun s _ => he₃ s) hS
  -- level 2
  have hG₂ : ∀ s ∈ Icc (0 : ℝ) t,
      0 ≤ (e₁ s - s * e₂ s - s ^ (2 : ℕ) * e₃ s) + 4 / 3 * S * s ^ (3 : ℕ) := by
    refine nonneg_of_deriv_nonneg_Icc (h' := fun s => -3 * s * e₃ s - s ^ (2 : ℕ) * e₄ s + 4 * S * s ^ (2 : ℕ))
      ht (by simp [he₁0]) (fun s _ => ?_) (fun s hs => ?_)
    · have := (((he₁ s).sub ((hasDerivAt_id s).mul (he₂ s))).sub
        ((hasDerivAt_pow 2 s).mul (he₃ s))).add ((hasDerivAt_pow 3 s).const_mul (4 / 3 * S))
      exact this.congr_deriv (by
        simp only [id_eq]; push_cast
        ring)
    · have h4 := (abs_le.mp (hS s hs)).2
      have h3' := (abs_le.mp (h3 s hs)).2
      have hs2 : 0 ≤ s ^ (2 : ℕ) := by positivity
      have := mul_le_mul_of_nonneg_left h4 hs2
      have := mul_le_mul_of_nonneg_left h3' hs.1
      nlinarith
  -- level 1
  have hG₁ : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ (s * e₁ s - s ^ (2 : ℕ) * e₂ s) + S * s ^ (4 : ℕ) / 3 := by
    refine nonneg_of_deriv_nonneg_Icc
      (h' := fun s => (e₁ s - s * e₂ s - s ^ (2 : ℕ) * e₃ s) + 4 / 3 * S * s ^ (3 : ℕ)) ht (by simp)
      (fun s _ => ?_) hG₂
    have := (((hasDerivAt_id s).mul (he₁ s)).sub ((hasDerivAt_pow 2 s).mul (he₂ s))).add
      (((hasDerivAt_pow 4 s).const_mul S).div_const 3)
    exact this.congr_deriv (by simp only [id_eq]; push_cast; ring)
  -- level 0
  have hG₀ : ∀ s ∈ Icc (0 : ℝ) t,
      0 ≤ (3 * s * e s - 3 * E s - s ^ (2 : ℕ) * e₁ s) + S * s ^ (5 : ℕ) / 15 := by
    refine nonneg_of_deriv_nonneg_Icc
      (h' := fun s => (s * e₁ s - s ^ (2 : ℕ) * e₂ s) + S * s ^ (4 : ℕ) / 3) ht (by simp [hE0])
      (fun s _ => ?_) hG₁
    have := (((((hasDerivAt_id s).const_mul (3 : ℝ)).mul (he s)).sub ((hE s).const_mul (3 : ℝ))).sub
      ((hasDerivAt_pow 2 s).mul (he₁ s))).add (((hasDerivAt_pow 5 s).const_mul S).div_const 15)
    exact this.congr_deriv (by simp only [id_eq]; push_cast; ring)
  have := hG₀ t ⟨ht, le_rfl⟩
  linarith

/-- **Sharp bound for the even kernel** `|3te − 3E − t²e₁| ≤ S t⁵/15`. -/
theorem abs_kernelTwo_le {e e₁ e₂ e₃ e₄ E : ℝ → ℝ} {S t : ℝ} (ht : 0 ≤ t)
    (hE : ∀ s, HasDerivAt E (e s) s) (he : ∀ s, HasDerivAt e (e₁ s) s)
    (he₁ : ∀ s, HasDerivAt e₁ (e₂ s) s) (he₂ : ∀ s, HasDerivAt e₂ (e₃ s) s)
    (he₃ : ∀ s, HasDerivAt e₃ (e₄ s) s)
    (hE0 : E 0 = 0) (he₁0 : e₁ 0 = 0) (he₃0 : e₃ 0 = 0)
    (hS : ∀ s ∈ Icc (0 : ℝ) t, |e₄ s| ≤ S) :
    |3 * t * e t - 3 * E t - t ^ (2 : ℕ) * e₁ t| ≤ S * t ^ (5 : ℕ) / 15 := by
  have hlow := kernelTwo_ge ht hE he he₁ he₂ he₃ hE0 he₁0 he₃0 hS
  have hup := kernelTwo_ge (e := fun s => -e s) (e₁ := fun s => -e₁ s) (e₂ := fun s => -e₂ s)
    (e₃ := fun s => -e₃ s) (e₄ := fun s => -e₄ s) (E := fun s => -E s) ht
    (fun s => (hE s).neg) (fun s => (he s).neg) (fun s => (he₁ s).neg) (fun s => (he₂ s).neg)
    (fun s => (he₃ s).neg) (by simp [hE0]) (by simp [he₁0]) (by simp [he₃0])
    (fun s hs => by simpa using hS s hs)
  rw [abs_le]
  constructor <;> linarith

/-! ## Instantiation for the frozen-jet kernels -/

theorem abs_fjEven_le_of_abs_le {c : ℝ → ℝ} {S u t : ℝ} (ht : 0 ≤ t)
    (hS : ∀ x ∈ Icc (u - t) (u + t), |c x| ≤ S) :
    ∀ s ∈ Icc (0 : ℝ) t, |fjEven c u s| ≤ S := by
  intro s hs
  unfold fjEven
  have h1 := hS (u + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h2 := hS (u - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [abs_div, abs_two]
  have := abs_add_le (c (u + s)) (c (u - s))
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **Sharp frozen-jet kernel bounds**: `|K₁| ≤ S₅ t⁶/90`, `|K₂| ≤ S₄ t⁵/15`. -/
theorem fj_kernel_bounds_sharp {σ c c₁ c₂ c₃ c₄ c₅ : ℝ → ℝ} {S₄ S₅ u t : ℝ} (ht : 0 ≤ t)
    (hσ : ∀ x, HasDerivAt σ (c x) x)
    (hc : ∀ x, HasDerivAt c (c₁ x) x) (hc₁ : ∀ x, HasDerivAt c₁ (c₂ x) x)
    (hc₂ : ∀ x, HasDerivAt c₂ (c₃ x) x) (hc₃ : ∀ x, HasDerivAt c₃ (c₄ x) x)
    (hc₄ : ∀ x, HasDerivAt c₄ (c₅ x) x)
    (hS₄ : ∀ x ∈ Icc (u - t) (u + t), |c₄ x| ≤ S₄) (hS₅ : ∀ x ∈ Icc (u - t) (u + t), |c₅ x| ≤ S₅) :
    |fjK₁ σ c c₁ u t| ≤ S₅ * t ^ (6 : ℕ) / 90 ∧ |fjK₂ σ c c₁ u t| ≤ S₄ * t ^ (5 : ℕ) / 15 := by
  constructor
  · unfold fjK₁
    exact abs_kernelOne_le (o := fjOdd c u) (o₁ := fjEven c₁ u) (o₂ := fjOdd c₂ u)
      (o₃ := fjEven c₃ u) (o₄ := fjOdd c₄ u) (o₅ := fjEven c₅ u) (O := fjO σ u) ht
      (hasDerivAt_fjO hσ u) (hasDerivAt_fjOdd hc u) (hasDerivAt_fjEven hc₁ u)
      (hasDerivAt_fjOdd hc₂ u) (hasDerivAt_fjEven hc₃ u) (hasDerivAt_fjOdd hc₄ u)
      (fjO_zero σ u) (fjOdd_zero c u) (fjOdd_zero c₂ u) (fjOdd_zero c₄ u)
      (abs_fjEven_le_of_abs_le ht hS₅)
  · unfold fjK₂
    exact abs_kernelTwo_le (e := fjEven c u) (e₁ := fjOdd c₁ u) (e₂ := fjEven c₂ u)
      (e₃ := fjOdd c₃ u) (e₄ := fjEven c₄ u) (E := fjE σ u) ht
      (hasDerivAt_fjE hσ u) (hasDerivAt_fjEven hc u) (hasDerivAt_fjOdd hc₁ u)
      (hasDerivAt_fjEven hc₂ u) (hasDerivAt_fjOdd hc₃ u)
      (fjE_zero σ u) (fjOdd_zero c₁ u) (fjOdd_zero c₃ u)
      (abs_fjEven_le_of_abs_le ht hS₄)

end RHTower
