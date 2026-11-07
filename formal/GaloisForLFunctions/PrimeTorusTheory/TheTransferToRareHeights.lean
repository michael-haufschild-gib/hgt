import GaloisForLFunctions.PrimeTorusTheory.LargeValueHeightsFormAnApproximateGroup

/-!
# The transfer to rare heights

A large value at one height generates large values at many heights, because the orbit returns. Partition the torus into `G^{|ι|}` cells. Among `J = G^{|ι|} m` equally spaced times, `m` lie in one cell, and their differences are returns of defect `≤ 2π² S/G²`. So:

**Theorem** (`exists_many_translates`). A height at level `θ` generates `m` heights at level `θ − 2π/G`, spaced by `Δ`, in a window of length `G^{|ι|} m Δ`.

**Transfer** (`not_mem_largeValue_of_count`). If typical heights are controlled, in the sense that no window of length `G^{|ι|} m Δ` contains `m` separated heights at level `θ`, then no height at all reaches the level `θ + 2π/G`.

**What this cannot do.** The inequality does not see the height: the window scales with `m`, and so does every count of large values that is linear in the window. And it is not empty only when `G^{|ι|}` is below the length of the window, which is the Kronecker scale `|ι| log G ≲ log T`. Past it there may be no return at all before time `T`. So translation carries typical bounds to rare heights only where the orbit already reaches every half-space: a saving at the rare heights has to come from integrality.
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

namespace PhaseSystem

variable {ι : Type*} [Fintype ι] (S : PhaseSystem ι)

/-- The cell of the torus containing a time. -/
noncomputable def cellOf {G : ℕ} (hG : 0 < G) (t : ℝ) (i : ι) : Fin G :=
  ⟨⌊(G : ℝ) * Int.fract (t * S.step i / (2 * Real.pi))⌋₊, by
    have hG' : (0 : ℝ) < G := by exact_mod_cast hG
    have h0 := Int.fract_nonneg (t * S.step i / (2 * Real.pi))
    have h1 := Int.fract_lt_one (t * S.step i / (2 * Real.pi))
    rw [Nat.floor_lt (by positivity)]
    nlinarith⟩

/-- Two times in one cell differ by a return. -/
theorem defect_sub_le_of_cell {G : ℕ} (hG : 0 < G) {t t' : ℝ} (h : S.cellOf hG t = S.cellOf hG t') :
    S.defect (t - t') ≤ S.size * (2 * Real.pi ^ 2 / (G : ℝ) ^ 2) := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  have hπ := Real.pi_pos
  rw [S.defect_eq_sum, size, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (S.weight_nonneg i)
  set u := t * S.step i / (2 * Real.pi) with hu
  set v := t' * S.step i / (2 * Real.pi) with hv
  have hcell : ⌊(G : ℝ) * Int.fract u⌋₊ = ⌊(G : ℝ) * Int.fract v⌋₊ := by
    have := congrFun h i
    exact congrArg Fin.val this
  have hu0 := Int.fract_nonneg u
  have hv0 := Int.fract_nonneg v
  have h1 := Nat.floor_le (by positivity : 0 ≤ (G : ℝ) * Int.fract u)
  have h2 := Nat.lt_floor_add_one ((G : ℝ) * Int.fract u)
  have h3 := Nat.floor_le (by positivity : 0 ≤ (G : ℝ) * Int.fract v)
  have h4 := Nat.lt_floor_add_one ((G : ℝ) * Int.fract v)
  rw [hcell] at h1 h2
  have hdiff : |(G : ℝ) * (Int.fract u - Int.fract v)| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  set d := Int.fract u - Int.fract v with hd
  have hd2 : (G : ℝ) ^ 2 * d ^ 2 ≤ 1 := by
    have := (sq_le_one_iff_abs_le_one _).mpr hdiff
    nlinarith
  -- The angle differs from `2π d` by a multiple of `2π`.
  have hangle : (t - t') * S.step i = 2 * Real.pi * d + (⌊u⌋ - ⌊v⌋ : ℤ) * (2 * Real.pi) := by
    have e1 : t * S.step i = 2 * Real.pi * u := by
      rw [hu]
      field_simp
    have e2 : t' * S.step i = 2 * Real.pi * v := by
      rw [hv]
      field_simp
    have e3 := Int.floor_add_fract u
    have e4 := Int.floor_add_fract v
    rw [sub_mul, e1, e2, hd]
    push_cast
    nlinarith
  rw [hangle, Real.cos_add_int_mul_two_pi]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * d)
  have hbound : (2 * Real.pi * d) ^ 2 / 2 ≤ 2 * Real.pi ^ 2 / (G : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : (2 * Real.pi * d) ^ 2 / 2 * (G : ℝ) ^ 2 = 2 * Real.pi ^ 2 * ((G : ℝ) ^ 2 * d ^ 2) := by ring
    rw [this]
    have h5 : 0 ≤ 2 * Real.pi ^ 2 := by positivity
    nlinarith
  linarith

/-- A return in a cell moves the column by at most `2πS/G`. -/
theorem le_column_add_of_defect_le {G : ℕ} (hG : 0 < G) {u : ℝ}
    (hu : S.defect u ≤ S.size * (2 * Real.pi ^ 2 / (G : ℝ) ^ 2)) (t : ℝ) :
    S.column t - 2 * Real.pi / G * S.size ≤ S.column (t + u) := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  have hπ := Real.pi_pos
  have hS := S.size_nonneg
  have h := S.column_sub_sq_le (t + u) t
  rw [add_sub_cancel_left] at h
  have hsq : (S.column (t + u) - S.column t) ^ 2 ≤ (2 * Real.pi / G * S.size) ^ 2 := by
    refine h.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * S.size)
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  have habs := abs_le_of_sq_le_sq' hsq (by positivity)
  linarith [habs.1]

/-- **A large value generates many.** See the module docstring. -/
theorem exists_many_translates {G m : ℕ} (hG : 0 < G) (hm : 1 ≤ m) {Δ θ t₀ : ℝ} (hΔ : 0 < Δ)
    (ht₀ : t₀ ∈ S.largeValue θ) :
    ∃ R : Finset ℝ, R.card = m ∧
      (∀ τ ∈ R, τ ∈ Set.Icc t₀ (t₀ + ((G ^ Fintype.card ι * m : ℕ) : ℝ) * Δ)) ∧
      (∀ τ ∈ R, τ ∈ S.largeValue (θ - 2 * Real.pi / G)) ∧
      ∀ τ ∈ R, ∀ τ' ∈ R, τ ≠ τ' → Δ ≤ |τ - τ'| := by
  classical
  set J : ℕ := G ^ Fintype.card ι * m with hJ
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  set f : ℕ → (ι → Fin G) := fun j => S.cellOf hG ((j : ℝ) * Δ) with hf
  haveI : Nonempty (Fin G) := ⟨⟨0, hG⟩⟩
  have hcardt : (Finset.univ : Finset (ι → Fin G)).card = G ^ Fintype.card ι := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := range J) (t := (Finset.univ : Finset (ι → Fin G))) (f := f) (n := m)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by
      rw [hcardt, Finset.card_range])
  obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq hy
  have hFne : F.Nonempty := by
    rw [← Finset.card_pos, hFcard]
    omega
  set j₀ := F.min' hFne with hj₀
  have hj₀mem : j₀ ∈ F := Finset.min'_mem _ _
  have hmem : ∀ j ∈ F, j < J ∧ f j = y := fun j hj => by
    have := Finset.mem_filter.mp (hFsub hj)
    exact ⟨Finset.mem_range.mp this.1, this.2⟩
  have hge : ∀ j ∈ F, j₀ ≤ j := fun j hj => Finset.min'_le _ _ hj
  set g : ℕ → ℝ := fun j => t₀ + ((j : ℝ) - j₀) * Δ with hg
  have hginj : Set.InjOn g (F : Set ℕ) := by
    intro a _ b _ h
    simp only [hg] at h
    have h1 : ((a : ℝ) - j₀) * Δ = ((b : ℝ) - j₀) * Δ := by linarith
    have h2 := mul_right_cancel₀ hΔ.ne' h1
    exact_mod_cast (by linarith : (a : ℝ) = b)
  refine ⟨F.image g, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hginj, hFcard]
  · intro τ hτ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hτ
    have h1 : (j₀ : ℝ) ≤ j := by exact_mod_cast hge j hj
    have h2 : (j : ℝ) ≤ J := by exact_mod_cast (hmem j hj).1.le
    have h3 : (0 : ℝ) ≤ j₀ := Nat.cast_nonneg _
    constructor
    · simp only [hg]
      nlinarith
    · simp only [hg]
      nlinarith
  · intro τ hτ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hτ
    have hcell : S.cellOf hG ((j : ℝ) * Δ) = S.cellOf hG ((j₀ : ℝ) * Δ) :=
      (hmem j hj).2.trans (hmem j₀ hj₀mem).2.symm
    have hdef := S.defect_sub_le_of_cell hG hcell
    have e : (j : ℝ) * Δ - (j₀ : ℝ) * Δ = ((j : ℝ) - j₀) * Δ := by ring
    rw [e] at hdef
    have h := S.le_column_add_of_defect_le hG hdef t₀
    rw [mem_largeValue]
    have h0 : θ * S.size ≤ S.column t₀ := ht₀
    simp only [hg]
    linarith
  · intro τ hτ τ' hτ' hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hτ'
    have hab : a ≠ b := fun h => hne (by rw [h])
    have e : g a - g b = ((a : ℝ) - b) * Δ := by
      simp only [hg]
      ring
    rw [e, abs_mul, abs_of_pos hΔ]
    have h1 : (1 : ℝ) ≤ |(a : ℝ) - b| := by
      have h2 : (1 : ℤ) ≤ |(a : ℤ) - b| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hab))
      exact_mod_cast h2
    nlinarith

/-- **The transfer.** A bound on the number of separated heights at level `θ` in a window excludes every height at level `θ + 2π/G`. -/
theorem not_mem_largeValue_of_count {G m : ℕ} (hG : 0 < G) (hm : 1 ≤ m) {Δ θ t₀ : ℝ} (hΔ : 0 < Δ)
    (hcount : ∀ R : Finset ℝ, (∀ τ ∈ R, τ ∈ Set.Icc t₀ (t₀ + ((G ^ Fintype.card ι * m : ℕ) : ℝ) * Δ)) →
      (∀ τ ∈ R, τ ∈ S.largeValue θ) → (∀ τ ∈ R, ∀ τ' ∈ R, τ ≠ τ' → Δ ≤ |τ - τ'|) → R.card < m) :
    t₀ ∉ S.largeValue (θ + 2 * Real.pi / G) := by
  intro h
  obtain ⟨R, hcard, h1, h2, h3⟩ := S.exists_many_translates hG hm hΔ h
  rw [add_sub_cancel_right] at h2
  exact absurd (hcount R h1 h2 h3) (by omega)

end PhaseSystem

end GaloisForLFunctions.PrimeTorusTheory
