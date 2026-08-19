import GaloisForLFunctions.HTGeometry.BaseFieldCollapse
import GaloisForLFunctions.HTGeometry.CassidySl2Classification

/-!
# From bounded line stabilisers to constant ones

The classification for `sl₂` asks that the scalars `c` with `c Z ∈ L` be constants, for `Z ∈ L` of
nonzero determinant.  What a differential-algebraic structure supplies instead is *boundedness*: a
fixed number of such scalars always admits a nontrivial relation over the base.  The two are the
same, and the bridge is the iterated bracket.

For traceless `Z` one has `Z² = -det(Z)·1`, hence `ad(Z)³ = 4δ · ad(Z)` with `δ = -det Z`.  Pick
`W ∈ L` with `ad(Z) W ≠ 0` — one exists because `L` spans `sl₂(U)` and `Z ≠ 0`.  Iterating the
bracket of `c Z` against `W` an odd number of times gives `c (δ c²)^k · ad(Z) W ∈ L` for every `k`,
and the same computation with `c = 1` gives `δ^k · ad(Z) W ∈ L`.  Boundedness of the stabiliser of
`ad(Z) W` therefore makes `δ` and `δ c²` algebraic over `C`, so `c²` and then `c` lie in `C`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C U : Type*} [Field C] [Field U] [Algebra C U]

/-- A subset of `U` is bounded over `C` when a fixed number of its elements always admits a
nontrivial `C`-linear relation. -/
def BoundedOverBase (C : Type*) [Field C] {U : Type*} [Field U] [Algebra C U] (S : Set U) : Prop :=
  ∃ N : ℕ, ∀ f : Fin (N + 1) → U, (∀ i, f i ∈ S) →
    ∃ g : Fin (N + 1) → C, (∃ i, g i ≠ 0) ∧ ∑ i, algebraMap C U (g i) * f i = 0

/-- **A power family inside a bounded set is algebraic over the base**, hence lies in it when the
base is algebraically closed. -/
theorem exists_eq_algebraMap_of_powers_mem [IsAlgClosed C] {S : Set U}
    (hS : BoundedOverBase C S) {b t : U} (hb : b ≠ 0) (hmem : ∀ k : ℕ, b * t ^ k ∈ S) :
    ∃ c₀ : C, t = algebraMap C U c₀ := by
  obtain ⟨N, hN⟩ := hS
  obtain ⟨g, hg, hrel⟩ := hN (fun i => b * t ^ (i : ℕ)) (fun i => hmem (i : ℕ))
  refine exists_eq_algebraMap_of_polynomial_relation hg ?_
  have hfac : b * ∑ i, algebraMap C U (g i) * t ^ (i : ℕ) = 0 := by
    rw [Finset.mul_sum, ← hrel]
    exact Finset.sum_congr rfl fun i _ => by ring
  exact (mul_eq_zero.mp hfac).resolve_left hb

/-! ### Iterated brackets -/

/-- The adjoint action of one matrix on another. -/
def adFun (Z B : Matrix (Fin 2) (Fin 2) U) : Matrix (Fin 2) (Fin 2) U := Z * B - B * Z

theorem adFun_smul_left (c : U) (Z B : Matrix (Fin 2) (Fin 2) U) :
    adFun (c • Z) B = c • adFun Z B := by
  simp only [adFun, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem adFun_smul_right (c : U) (Z B : Matrix (Fin 2) (Fin 2) U) :
    adFun Z (c • B) = c • adFun Z B := by
  simp only [adFun, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem iterate_adFun_smul (c : U) (Z : Matrix (Fin 2) (Fin 2) U) :
    ∀ (k : ℕ) (B : Matrix (Fin 2) (Fin 2) U),
      (adFun (c • Z))^[k] B = (c ^ k) • ((adFun Z)^[k] B) := by
  intro k
  induction k with
  | zero => intro B; simp
  | succ k ih =>
      intro B
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih B, adFun_smul_left,
        adFun_smul_right, smul_smul, pow_succ]
      ring_nf

/-- **The cube of the adjoint action of a traceless matrix.** -/
theorem adFun_cube {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z.trace = 0)
    (B : Matrix (Fin 2) (Fin 2) U) :
    adFun Z (adFun Z (adFun Z B)) = (4 * (-Z.det)) • adFun Z B := by
  have h11 : Z 1 1 = -(Z 0 0) := by
    rw [Matrix.trace_fin_two] at hZ
    linear_combination hZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [adFun, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, Matrix.det_fin_two] <;>
    simp [h11] <;> ring

theorem iterate_adFun_odd {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z.trace = 0)
    (B : Matrix (Fin 2) (Fin 2) U) :
    ∀ k : ℕ, (adFun Z)^[2 * k + 1] B = ((4 * (-Z.det)) ^ k) • adFun Z B := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
      rw [hstep, Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        adFun_smul_right, adFun_smul_right, adFun_cube hZ, smul_smul, pow_succ]

theorem iterate_adFun_mem (L : Submodule C (Matrix (Fin 2) (Fin 2) U))
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    {X : Matrix (Fin 2) (Fin 2) U} (hX : X ∈ L) :
    ∀ (k : ℕ) {B : Matrix (Fin 2) (Fin 2) U}, B ∈ L → (adFun X)^[k] B ∈ L := by
  intro k
  induction k with
  | zero => intro B hB; simpa using hB
  | succ k ih =>
      intro B hB
      rw [Function.iterate_succ_apply']
      exact hbr X hX _ (ih hB)

/-- **The line stabilisers of a spanning bracket-closed subspace are constant** as soon as they are
bounded over the base.  The iterated bracket identity `ad(Z)³ = 4δ ad(Z)` puts the whole power
family `c (δ c²)^k` inside one stabiliser, so `δ` and `δ c²` are algebraic over `C`, and hence so
is `c`. -/
theorem line_stabiliser_mem_base [IsAlgClosed C] [CharZero U]
    (L : Submodule C (Matrix (Fin 2) (Fin 2) U))
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    (hbound : ∀ Y ∈ L, Y ≠ 0 → BoundedOverBase C {c : U | c • Y ∈ L})
    {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z ∈ L) (hZtr : Z.trace = 0) (hZdet : Z.det ≠ 0)
    {c : U} (hc : c • Z ∈ L) :
    ∃ c₀ : C, c = algebraMap C U c₀ := by
  classical
  rcases eq_or_ne c 0 with rfl | hcne
  · exact ⟨0, by rw [map_zero]⟩
  have h11 : Z 1 1 = -(Z 0 0) := by
    rw [Matrix.trace_fin_two] at hZtr
    linear_combination hZtr
  obtain ⟨W, hW, hWne⟩ : ∃ W ∈ L, adFun Z W ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hker : ∀ B ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)), adFun Z B = 0 := by
      intro B hB
      induction hB using Submodule.span_induction with
      | mem y hy => exact hcon y hy
      | zero => simp [adFun]
      | add y z _ _ hy hz =>
          have heq : adFun Z (y + z) = adFun Z y + adFun Z z := by
            simp only [adFun, Matrix.mul_add, Matrix.add_mul]
            abel
          rw [heq, hy, hz, add_zero]
      | smul u y _ hy =>
          rw [adFun_smul_right, hy, smul_zero]
    have hE := hker (sl2E U) (hdense _ (by simp [sl2E, Matrix.trace_fin_two]))
    have hF := hker (sl2F U) (hdense _ (by simp [sl2F, Matrix.trace_fin_two]))
    have hE00 := congrFun (congrFun hE 0) 0
    have hE01 := congrFun (congrFun hE 0) 1
    have hF00 := congrFun (congrFun hF 0) 0
    simp only [adFun, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.zero_apply] at hE00 hE01 hF00
    simp [sl2E, sl2F] at hE00 hE01 hF00
    apply hZdet
    have hz00 : Z 0 0 = 0 := by
      rw [h11] at hE01
      have h2 : (2 : U) * Z 0 0 = 0 := by linear_combination hE01
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h
    rw [Matrix.det_fin_two, h11, hz00, hE00, hF00]
    ring
  have hYL : adFun Z W ∈ L := hbr Z hZ W hW
  set δ : U := 4 * (-Z.det) with hδ
  have hδne : δ ≠ 0 := by
    rw [hδ]
    exact mul_ne_zero (by norm_num) (neg_ne_zero.mpr hZdet)
  have hmem1 : ∀ k : ℕ, (1 : U) * δ ^ k ∈ {t : U | t • adFun Z W ∈ L} := by
    intro k
    have hmemL : (adFun Z)^[2 * k + 1] W ∈ L := iterate_adFun_mem L hbr hZ _ hW
    rw [iterate_adFun_odd hZtr W k] at hmemL
    show ((1 : U) * δ ^ k) • adFun Z W ∈ L
    rw [one_mul]
    exact hmemL
  have hmemc : ∀ k : ℕ, c * (δ * c ^ 2) ^ k ∈ {t : U | t • adFun Z W ∈ L} := by
    intro k
    have hmemL : (adFun (c • Z))^[2 * k + 1] W ∈ L := iterate_adFun_mem L hbr hc _ hW
    rw [iterate_adFun_smul c Z (2 * k + 1) W, iterate_adFun_odd hZtr W k, smul_smul] at hmemL
    have hval : ∀ d : U, c ^ (2 * k + 1) * d ^ k = c * (d * c ^ 2) ^ k := by
      intro d
      rw [mul_pow]
      ring
    rw [hval δ] at hmemL
    exact hmemL
  obtain ⟨d₀, hd₀⟩ :=
    exists_eq_algebraMap_of_powers_mem (hbound _ hYL hWne) one_ne_zero hmem1
  obtain ⟨e₀, he₀⟩ :=
    exists_eq_algebraMap_of_powers_mem (hbound _ hYL hWne) hcne hmemc
  have hd₀ne : d₀ ≠ 0 := by
    intro h0
    apply hδne
    rw [hd₀, h0, map_zero]
  have hd₀U : algebraMap C U d₀ ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap C U) (algebraMap C U).injective).mpr hd₀ne
  have hc2 : c ^ 2 = algebraMap C U (e₀ / d₀) := by
    rw [map_div₀, eq_div_iff hd₀U, ← hd₀, ← he₀]
    ring
  exact exists_eq_algebraMap_of_sq hc2

/-- **Cassidy's classification for `sl₂` under bounded line stabilisers.** -/
theorem cassidy_sl2_of_bounded [IsAlgClosed C] [IsAlgClosed U] [CharZero U]
    (L : Submodule C (Matrix (Fin 2) (Fin 2) U))
    (htr : ∀ A ∈ L, A.trace = 0)
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    (hbound : ∀ Y ∈ L, Y ≠ 0 → BoundedOverBase C {c : U | c • Y ∈ L}) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) U, P * Q = 1 ∧ Q * P = 1 ∧
      L.map (conjLinear C P Q) = Submodule.span C {sl2H U, sl2E U, sl2F U} :=
  cassidy_sl2 L htr hbr hdense fun A hA hAdet _ hc =>
    line_stabiliser_mem_base L hbr hdense hbound hA (htr A hA) hAdet hc

end

end GaloisForLFunctions.HTGeometry
