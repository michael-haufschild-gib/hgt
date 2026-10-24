import GaloisForLFunctions.ArithmeticOrientationTheory.UnpayabilityIsLocatedOnTheBohrPolydisk

/-!
# The calculus of the obstruction hull

The obstruction hull of a weight `c` (`obstructionHull`, `UnpayabilityIsLocatedOnTheBohrPolydisk`)
is the set of Bohr points at which every repairing kernel vanishes.  Its basic algebra:

* **Real weights have conjugation-symmetric hulls** (`conj_mem_obstructionHull`): the repairing
  ideal is closed under conjugation of kernels, and `(k̄)^(ω̄) = conj(k̂(ω))`.  This is why the
  oscillating probe is obstructed at the pair `{ρ, ρ̄}`.
* **Sums** (`obstructionHull_add_subset`): `hull(c + c') ⊆ hull(c) ∪ hull(c')`; a point outside
  both hulls is avoided by the product of two repairing kernels, which repairs the sum.
* **Cancellation** (`mem_obstructionHull_add_of_not_mem`): obstructions of a sum cancel only at
  common points, `hull(c) △ hull(c') ⊆ hull(c + c')`.
* **Scaling** (`obstructionHull_smul`): `hull(t c) = hull(c)` for `t ≠ 0`.
* **Convolution is local** (`obstructionHull_conv_subset`, `mem_obstructionHull_conv`):
  `hull(k₀ ⋆ c) ⊆ hull(c)`, and every point of `hull(c)` at which `k̂₀` does not vanish stays in
  `hull(k₀ ⋆ c)`.  A kernel can repair an obstruction only at its own zeros, and it repairs `c`
  only if it vanishes on the whole hull.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Conjugate kernels and conjugate Bohr points -/

/-- The conjugate Bohr point `ω̄`. -/
def BohrPoint.conj (ω : BohrPoint) : BohrPoint where
  ω n := starRingEnd ℂ (ω.ω n)
  map_one := by rw [ω.map_one, _root_.map_one]
  map_mul m n := by rw [ω.map_mul, _root_.map_mul]
  norm_le_one n := by rw [Complex.norm_conj]; exact ω.norm_le_one n

/-- The conjugate arithmetic function. -/
def conjFn (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => starRingEnd ℂ (f n), by simp⟩

theorem lSeriesSummable_conjFn {f : ArithmeticFunction ℂ} {σ : ℝ} (hf : LSeriesSummable (⇑f) σ) :
    LSeriesSummable (⇑(conjFn f)) σ := by
  rw [← summable_norm_term_iff] at hf ⊢
  refine hf.congr fun n => ?_
  rw [norm_term_eq, norm_term_eq]
  simp [conjFn]

/-- The conjugate of an element of `𝒲_{1/2}`. -/
def conjW (k : WienerAlgebraAt (1 / 2)) : WienerAlgebraAt (1 / 2) :=
  mk (conjFn k.toFn) (lSeriesSummable_conjFn k.summable)

theorem rePart_conjW (k : WienerAlgebraAt (1 / 2)) : rePart (conjW k) = rePart k :=
  funext fun n => by simp [rePart, conjW, toFn_mk, conjFn]

theorem imPart_conjW (k : WienerAlgebraAt (1 / 2)) : imPart (conjW k) = fun n => -imPart k n :=
  funext fun n => by simp [imPart, conjW, toFn_mk, conjFn]

theorem dirichletConv_neg_left (a c : ℕ → ℝ) :
    RHTower.dirichletConv (fun n => -a n) c = fun n => -RHTower.dirichletConv a c n := by
  funext n
  unfold RHTower.dirichletConv
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- `(k̄)^(ω̄) = conj(k̂(ω))`. -/
theorem bohrEval_conj (k : WienerAlgebraAt (1 / 2)) (ω : BohrPoint) :
    bohrEval (1 / 2) (conjW k).toFn ω.conj = starRingEnd ℂ (bohrEval (1 / 2) k.toFn ω) := by
  unfold bohrEval LSeries
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn, map_div₀, map_mul]
  have hc : starRingEnd ℂ ((n : ℂ) ^ (((1 / 2 : ℝ)) : ℂ)) = (n : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.conj_ofReal]
  rw [hc]
  rfl

/-- **Real weights have conjugation-symmetric obstruction hulls.** -/
theorem conj_mem_obstructionHull (c : ℕ → ℝ) (hc : Summable fun d : ℕ => |c d / d|) {ω : BohrPoint}
    (hω : ω ∈ obstructionHull c hc) : ω.conj ∈ obstructionHull c hc := by
  intro k hk
  have hk' : conjW k ∈ paidIdeal c hc := by
    rw [mem_paidIdeal] at hk ⊢
    rw [rePart_conjW, imPart_conjW, dirichletConv_neg_left, receiverBounded_neg]
    exact hk
  have h := hω (conjW k) hk'
  have h2 := bohrEval_conj (conjW k) ω
  have hkk : conjW (conjW k) = k := ext fun n => by simp [conjW, toFn_mk, conjFn]
  rw [hkk, h, _root_.map_zero] at h2
  exact h2

/-! ### Sums and scaling -/

theorem dirichletConv_add_right' (a c c' : ℕ → ℝ) :
    RHTower.dirichletConv a (fun n => c n + c' n) =
      fun n => RHTower.dirichletConv a c n + RHTower.dirichletConv a c' n := by
  funext n
  unfold RHTower.dirichletConv
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

theorem summable_abs_add_div {c c' : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) : Summable fun d : ℕ => |(c d + c' d) / d| :=
  (hc.add hc').of_nonneg_of_le (fun _ => abs_nonneg _) fun d => by
    rw [add_div]; exact abs_add_le _ _

/-- A kernel repairing both `c` and `c'` repairs `c + c'`. -/
theorem paidIdeal_inf_le_add {c c' : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) :
    paidIdeal c hc ⊓ paidIdeal c' hc' ≤ paidIdeal (fun n => c n + c' n) (summable_abs_add_div hc hc') := by
  intro k hk
  obtain ⟨hk, hk'⟩ := Submodule.mem_inf.1 hk
  rw [mem_paidIdeal] at hk hk' ⊢
  rw [dirichletConv_add_right', dirichletConv_add_right']
  exact ⟨receiverBounded_add (summable_abs_dirichletConv_div (criticalWiener_rePart k) hc).of_abs
      (summable_abs_dirichletConv_div (criticalWiener_rePart k) hc').of_abs hk.1 hk'.1,
    receiverBounded_add (summable_abs_dirichletConv_div (criticalWiener_imPart k) hc).of_abs
      (summable_abs_dirichletConv_div (criticalWiener_imPart k) hc').of_abs hk.2 hk'.2⟩

/-- **Obstructions do not appear from nowhere**: `hull(c + c') ⊆ hull(c) ∪ hull(c')`. -/
theorem obstructionHull_add_subset {c c' : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) :
    obstructionHull (fun n => c n + c' n) (summable_abs_add_div hc hc') ⊆
      obstructionHull c hc ∪ obstructionHull c' hc' := by
  intro ω hω
  by_contra hno
  simp only [Set.mem_union, not_or] at hno
  obtain ⟨h1, h2⟩ := hno
  simp only [obstructionHull, Set.mem_setOf_eq, not_forall] at h1 h2
  obtain ⟨k₁, hk₁, hv₁⟩ := h1
  obtain ⟨k₂, hk₂, hv₂⟩ := h2
  have hk : k₁ * k₂ ∈ paidIdeal (fun n => c n + c' n) (summable_abs_add_div hc hc') :=
    paidIdeal_inf_le_add hc hc' ⟨Ideal.mul_mem_right _ _ hk₁, Ideal.mul_mem_left _ _ hk₂⟩
  have h := hω _ hk
  rw [← bohrCharacter_apply, _root_.map_mul, bohrCharacter_apply, bohrCharacter_apply] at h
  exact (mul_ne_zero hv₁ hv₂) h

theorem summable_abs_smul_div {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) (t : ℝ) :
    Summable fun d : ℕ => |t * c d / d| :=
  (hc.mul_left |t|).congr fun d => by rw [mul_div_assoc, abs_mul]

theorem paidIdeal_smul {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) {t : ℝ} (ht : t ≠ 0) :
    paidIdeal (fun n => t * c n) (summable_abs_smul_div hc t) = paidIdeal c hc := by
  ext k
  rw [mem_paidIdeal, mem_paidIdeal]
  have key : ∀ f : ℕ → ℝ, RHTower.dirichletConv f (fun n => t * c n) =
      fun n => t * RHTower.dirichletConv f c n := fun f => funext fun n => by
    unfold RHTower.dirichletConv; rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [key, key, receiverBounded_smul_iff ht, receiverBounded_smul_iff ht]

/-- **Scaling does not move the hull.** -/
theorem obstructionHull_smul {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) {t : ℝ}
    (ht : t ≠ 0) :
    obstructionHull (fun n => t * c n) (summable_abs_smul_div hc t) = obstructionHull c hc := by
  unfold obstructionHull
  rw [paidIdeal_smul hc ht]

theorem mem_paidIdeal_congr {c c' : ℕ → ℝ} (h : c = c') (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal c hc ↔ k ∈ paidIdeal c' hc' := by
  subst h; rfl

/-- **Obstructions cancel only where both hulls meet**: a point of `hull(c)` outside `hull(c')` is
a point of `hull(c + c')`.  With `obstructionHull_add_subset`,
`hull(c) △ hull(c') ⊆ hull(c + c') ⊆ hull(c) ∪ hull(c')`. -/
theorem mem_obstructionHull_add_of_not_mem {c c' : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) {ω : BohrPoint} (hω : ω ∈ obstructionHull c hc)
    (hω' : ω ∉ obstructionHull c' hc') :
    ω ∈ obstructionHull (fun n => c n + c' n) (summable_abs_add_div hc hc') := by
  intro k hk
  simp only [obstructionHull, Set.mem_setOf_eq, not_forall] at hω'
  obtain ⟨k', hk', hv'⟩ := hω'
  -- `k k'` repairs `c + c'` and `−c'`, hence their sum `c`.
  have h1 : k * k' ∈ paidIdeal (fun n => c n + c' n) (summable_abs_add_div hc hc') :=
    Ideal.mul_mem_right _ _ hk
  have h2 : k * k' ∈ paidIdeal (fun n => -1 * c' n) (summable_abs_smul_div hc' (-1)) := by
    rw [paidIdeal_smul hc' (by norm_num)]; exact Ideal.mul_mem_left _ _ hk'
  have h3 := paidIdeal_inf_le_add (summable_abs_add_div hc hc') (summable_abs_smul_div hc' (-1))
    (Submodule.mem_inf.2 ⟨h1, h2⟩)
  have h4 : k * k' ∈ paidIdeal c hc :=
    (mem_paidIdeal_congr (funext fun n => by ring) _ hc _).1 h3
  have h := hω _ h4
  rw [← bohrCharacter_apply, _root_.map_mul, bohrCharacter_apply, bohrCharacter_apply] at h
  exact (mul_eq_zero.1 h).resolve_right hv'

/-! ### Convolution is local -/

/-- The repairing ideal of `k₀ ⋆ c` is the ideal quotient: `k` repairs `k₀ ⋆ c` iff `k k₀`
repairs `c`. -/
theorem mem_paidIdeal_conv_iff (c : ℕ → ℝ) (hc : Summable fun d : ℕ => |c d / d|) {k₀ : ℕ → ℝ}
    (hk₀ : CriticalWiener k₀) (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) ↔
      k * toWiener k₀ hk₀ ∈ paidIdeal c hc := by
  have hr : rePart (toWiener k₀ hk₀) = fun n => if n = 0 then 0 else k₀ n := funext fun n => by
    rcases eq_or_ne n 0 with rfl | hn <;> simp [rePart, toWiener, toFn_mk, realFn, *]
  have hi : imPart (toWiener k₀ hk₀) = fun _ => 0 := funext fun n => by
    rcases eq_or_ne n 0 with rfl | hn <;> simp [imPart, toWiener, toFn_mk, realFn, *]
  have hconv : ∀ f : ℕ → ℝ, RHTower.dirichletConv f (fun n => if n = 0 then 0 else k₀ n) =
      RHTower.dirichletConv f k₀ := fun f => funext fun n =>
    dirichletConv_congr (fun _ _ => rfl) (fun m hm => if_neg hm) n
  rw [mem_paidIdeal, mem_paidIdeal]
  have e0 : rePart (k * toWiener k₀ hk₀) = fun n => RHTower.dirichletConv (rePart k) k₀ n := by
    funext n
    rw [rePart_mul, hr, hi, hconv]
    simp [RHTower.dirichletConv]
  have e1 : imPart (k * toWiener k₀ hk₀) = fun n => RHTower.dirichletConv (imPart k) k₀ n := by
    funext n
    rw [imPart_mul, hr, hi, hconv]
    simp [RHTower.dirichletConv]
  rw [e0, e1, ← dirichletConv_assoc, ← dirichletConv_assoc]

/-- **Convolution only removes obstructions**: `hull(k₀ ⋆ c) ⊆ hull(c)`. -/
theorem obstructionHull_conv_subset (c : ℕ → ℝ) (hc : Summable fun d : ℕ => |c d / d|) {k₀ : ℕ → ℝ}
    (hk₀ : CriticalWiener k₀) :
    obstructionHull (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) ⊆
      obstructionHull c hc := fun _ hω k hk =>
  hω k ((mem_paidIdeal_conv_iff c hc hk₀ k).2 (Ideal.mul_mem_right _ _ hk))

/-- **Convolution removes an obstruction only at its own zeros**: a point of `hull(c)` at which
`k̂₀` does not vanish is a point of `hull(k₀ ⋆ c)`. -/
theorem mem_obstructionHull_conv (c : ℕ → ℝ) (hc : Summable fun d : ℕ => |c d / d|) {k₀ : ℕ → ℝ}
    (hk₀ : CriticalWiener k₀) {ω : BohrPoint} (hω : ω ∈ obstructionHull c hc)
    (hne : bohrEval (1 / 2) (toWiener k₀ hk₀).toFn ω ≠ 0) :
    ω ∈ obstructionHull (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) := by
  intro k hk
  have h := hω _ ((mem_paidIdeal_conv_iff c hc hk₀ k).1 hk)
  rw [← bohrCharacter_apply, _root_.map_mul, bohrCharacter_apply, bohrCharacter_apply] at h
  exact (mul_eq_zero.1 h).resolve_right hne

end

end GaloisForLFunctions.ArithmeticOrientationTheory
