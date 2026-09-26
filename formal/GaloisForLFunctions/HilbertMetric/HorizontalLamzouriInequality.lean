import Mathlib

/-!
# Horizontal refinement of Lamzouri's Hilbert-space inequality

Lamzouri's argument for simple zeros places the vectors of a conjugation-invariant multiset in a
real inner product space: a real point `x` of multiplicity `m` contributes `m · f_x ⊗ f_x` with
`‖f_x‖ = 1`, and a conjugate pair `z, z̄` of multiplicity `m` contributes
`2m · (g_z ⊗ g_z − h_z ⊗ h_z)` with `‖g_z‖² − ‖h_z‖² = 1`.  The energy of the packet is
`E = Σ_{k,l} c_k c_l ⟪w_k, w_l⟫²`, and its mass `N = Σ_k c_k ‖w_k‖²` is the number of points.
Lamzouri proves that the number of simple real points is at least `2N − E`.

Here the simple real points are split into *horizontally simple* points `fH` and *mixed* points
`fM` (in the application: a simple zero on the critical line that shares its ordinate with an
off-line pair).  Put `A = span(f_mult, g)`, `C = A ⊔ span fH`, `B = C ⊔ span fM` and
`W = B ⊔ span h`.  An orthonormal frame adapted to `A ≤ C ≤ B ≤ W` gives

`2N − #H − #M + 2T + 4Λ ≤ E`  (`energy_lower_bound`),

`T² ≤ #M · (E − (2N − #H − #M + 2T + 4Λ))`  (`mixedOverlap_sq_le`),

where `T = Σ_{x ∈ M} ‖P_A f_x‖²` is the overlap of the mixed points with the absorbing span and
`Λ = Σ_p m_p (‖P_{A^⊥} h_p‖² + ‖P_{B^⊥} h_p‖²)` is the part of the negative vectors that the
positive ones fail to absorb.  Consequently the horizontally simple points alone satisfy
Lamzouri's bound whenever `#M² ≤ #M(2T + 4Λ) + T²` (`card_hs_ge_of_overlap`); in particular
when every mixed point has overlap at least `√2 − 1`.  A mixed point's own pair vector `g`
lies in `A`, so `T ≥ Σ_x ⟪f_x, g⟫² / ‖g‖²` (`mixedOverlap_ge_ownPair`).

No linear independence is assumed and the ambient space may be infinite-dimensional.
-/

open scoped RealInnerProductSpace
open Finset Module

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Frames adapted to a flag of finite-dimensional subspaces -/

/-- Parseval on a finite-dimensional subspace, through its standard orthonormal basis. -/
theorem sum_inner_mul_inner_stdOrthonormalBasis (K : Submodule ℝ V) [FiniteDimensional ℝ K]
    (u v : V) :
    ∑ j, ⟪u, ((stdOrthonormalBasis ℝ K) j : V)⟫ * ⟪v, ((stdOrthonormalBasis ℝ K) j : V)⟫ =
      ⟪K.starProjection u, v⟫ := by
  set b := stdOrthonormalBasis ℝ K
  have key : ∀ x : V, ∀ j, ⟪x, (b j : V)⟫ = ⟪K.orthogonalProjectionOnto x, b j⟫ := fun x j =>
    (K.inner_orthogonalProjectionOnto_eq_of_mem_right (b j) x).symm
  have hj : ∀ j, ⟪u, (b j : V)⟫ * ⟪v, (b j : V)⟫ =
      ⟪K.orthogonalProjectionOnto u, b j⟫ * ⟪b j, K.orthogonalProjectionOnto v⟫ := fun j => by
    rw [key u j, key v j, real_inner_comm (b j) (K.orthogonalProjectionOnto v)]
  rw [Finset.sum_congr rfl fun j _ => hj j, b.sum_inner_mul_inner,
    K.inner_orthogonalProjectionOnto_eq_of_mem_left, ← Submodule.starProjection_apply]

/-- The squared coordinates of a vector in the standard basis of a subspace sum to the squared
norm of its projection. -/
theorem sum_sq_inner_stdOrthonormalBasis (K : Submodule ℝ V) [FiniteDimensional ℝ K] (x : V) :
    ∑ j, ⟪x, ((stdOrthonormalBasis ℝ K) j : V)⟫ ^ 2 = ‖K.starProjection x‖ ^ 2 := by
  have h := sum_inner_mul_inner_stdOrthonormalBasis K x x
  simp_rw [← sq] at h
  rw [h]
  have hidem : K.starProjection (K.starProjection x) = K.starProjection x :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
  have h2 : ⟪K.starProjection x, x⟫ = ⟪K.starProjection x, K.starProjection x⟫ := by
    conv_lhs => rw [← hidem]
    exact K.inner_starProjection_left_eq_right _ _
  rw [h2, real_inner_self_eq_norm_sq]

/-- Along `K ≤ K'`, the projection onto `K'` is the projection onto `K` plus the projection onto
the relative complement `Kᗮ ⊓ K'`. -/
theorem starProjection_eq_add_starProjection_inf_orthogonal {K K' : Submodule ℝ V}
    [FiniteDimensional ℝ K'] (h : K ≤ K') (u : V) :
    haveI : FiniteDimensional ℝ K := Submodule.finiteDimensional_of_le h
    haveI : FiniteDimensional ℝ (Kᗮ ⊓ K' : Submodule ℝ V) :=
      Submodule.finiteDimensional_of_le inf_le_right
    K'.starProjection u = K.starProjection u + (Kᗮ ⊓ K').starProjection u := by
  haveI : FiniteDimensional ℝ K := Submodule.finiteDimensional_of_le h
  haveI : FiniteDimensional ℝ (Kᗮ ⊓ K' : Submodule ℝ V) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hmem : K'.starProjection u - K.starProjection u ∈ Kᗮ ⊓ K' := by
    refine Submodule.mem_inf.mpr
      ⟨?_, K'.sub_mem (K'.starProjection_apply_mem u) (h (K.starProjection_apply_mem u))⟩
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [inner_sub_right, ← K'.inner_starProjection_left_eq_right,
      K'.starProjection_eq_self_iff.mpr (h hk), ← K.inner_starProjection_left_eq_right,
      K.starProjection_eq_self_iff.mpr hk, sub_self]
  have heq : (Kᗮ ⊓ K').starProjection u = K'.starProjection u - K.starProjection u := by
    apply Submodule.eq_starProjection_of_mem_orthogonal hmem
    rw [Submodule.mem_orthogonal]
    intro z hz
    have h1 : ⟪z, u - K'.starProjection u⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.mem_inf.mp hz).2
        (K'.sub_starProjection_mem_orthogonal u)
    have h2 : ⟪z, K.starProjection u⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (K.starProjection_apply_mem u)
        (Submodule.mem_inf.mp hz).1
    rw [show u - (K'.starProjection u - K.starProjection u) =
        (u - K'.starProjection u) + K.starProjection u by abel, inner_add_right, h1, h2, add_zero]
  rw [heq]; abel

/-- **Diagonal Bessel bound.** If a finite family `b` reproduces the inner products of the
vectors `w`, the diagonal entries of the weighted form `Σ c_k w_k ⊗ w_k` in `b` have squared sum
at most the energy `Σ_{k,l} c_k c_l ⟪w_k, w_l⟫²`. -/
theorem sum_sq_diag_le_energy {S κ : Type*} [Fintype S] [Fintype κ] (b : S → V) (w : κ → V)
    (hb : ∀ k l, ∑ s, ⟪w k, b s⟫ * ⟪w l, b s⟫ = ⟪w k, w l⟫) (c : κ → ℝ) :
    ∑ s, (∑ k, c k * ⟪w k, b s⟫ ^ 2) ^ 2 ≤ ∑ k, ∑ l, c k * c l * ⟪w k, w l⟫ ^ 2 := by
  set a : κ → S → ℝ := fun k s => ⟪w k, b s⟫ with ha
  have e1 : ∀ k l, ⟪w k, w l⟫ ^ 2 =
      ∑ s, ∑ s', (a k s * a k s') * (a l s * a l s') := by
    intro k l
    rw [← hb k l, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    simp only [ha]; ring
  calc ∑ s, (∑ k, c k * ⟪w k, b s⟫ ^ 2) ^ 2
      ≤ ∑ s, ∑ s', (∑ k, c k * (a k s * a k s')) ^ 2 := by
        refine Finset.sum_le_sum fun s _ => ?_
        have hs : (∑ k, c k * ⟪w k, b s⟫ ^ 2) ^ 2 = (∑ k, c k * (a k s * a k s)) ^ 2 := by
          simp only [ha, sq]
        rw [hs]
        exact Finset.single_le_sum (f := fun s' => (∑ k, c k * (a k s * a k s')) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ s)
    _ = ∑ s, ∑ s', ∑ k, ∑ l, (c k * (a k s * a k s')) * (c l * (a l s * a l s')) := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ s, ∑ k, ∑ s', ∑ l, (c k * (a k s * a k s')) * (c l * (a l s * a l s')) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ k, ∑ s, ∑ s', ∑ l, (c k * (a k s * a k s')) * (c l * (a l s * a l s')) :=
        Finset.sum_comm
    _ = ∑ k, ∑ s, ∑ l, ∑ s', (c k * (a k s * a k s')) * (c l * (a l s * a l s')) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ s, ∑ s', (c k * (a k s * a k s')) * (c l * (a l s * a l s')) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, c k * c l * ⟪w k, w l⟫ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring

/-! ### Scalar estimates for one range -/

/-- Completing the square around a centre `c`. -/
theorem sum_sq_ge_of_center {d : ℕ} (α : Fin d → ℝ) (c : ℝ) :
    2 * c * ∑ j, α j - c ^ 2 * d ≤ ∑ j, α j ^ 2 := by
  have h := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (α j - c)
  have e : ∑ j, (α j - c) ^ 2 = ∑ j, α j ^ 2 - 2 * c * ∑ j, α j + c ^ 2 * d := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

/-- **The mixed range.** If `d ≤ n` diagonal values have sum at most `n − T` with `0 ≤ T ≤ n`,
then `T² ≤ n (Σ α² − 2 Σ α + n)`. -/
theorem sq_le_card_mul_of_sum_le {d : ℕ} (α : Fin d → ℝ) {n T : ℝ} (hd : (d : ℝ) ≤ n)
    (hT0 : 0 ≤ T) (hTn : T ≤ n) (hs : ∑ j, α j ≤ n - T) :
    T ^ 2 ≤ n * (∑ j, α j ^ 2 - 2 * ∑ j, α j + n) := by
  set s := ∑ j, α j with hsdef
  set D := ∑ j, (α j - 1) ^ 2 with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hDexp : ∑ j, α j ^ 2 - 2 * s + n = D + (n - d) := by
    have : D = ∑ j, α j ^ 2 - 2 * s + d := by
      simp only [hDdef, hsdef, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hCS : ((d : ℝ) - s) ^ 2 ≤ d * D := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => 1 - α j)
    have e1 : ∑ j : Fin d, (1 - α j) = d - s := by
      simp [Finset.sum_sub_distrib, hsdef]
    have e2 : ∑ j : Fin d, (1 - α j) ^ 2 = D := by
      simp only [hDdef]; exact Finset.sum_congr rfl fun j _ => by ring
    simpa [e1, e2] using h
  rw [hDexp]
  set δ := n - d with hδ
  have hδ0 : 0 ≤ δ := by linarith
  by_cases hTδ : T ≤ δ
  · have : n * δ ≤ n * (D + δ) := by
      have hn : 0 ≤ n := by linarith
      nlinarith
    nlinarith
  · replace hTδ : δ < T := lt_of_not_ge hTδ
    have hgap : T - δ ≤ d - s := by linarith
    have h1 : (T - δ) ^ 2 ≤ d * D := by
      have : (T - δ) ^ 2 ≤ ((d : ℝ) - s) ^ 2 := pow_le_pow_left₀ (by linarith) hgap 2
      linarith
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h2 : 2 * (T - δ) ≤ D + d := by
      nlinarith [sq_nonneg (D - d), sq_nonneg (D + d - 2 * (T - δ))]
    have hn : n = d + δ := by linarith
    rw [hn]
    nlinarith [mul_le_mul_of_nonneg_left h2 hδ0]

/-- The own-pair overlap: for `a ∈ K`, `⟪v, a⟫² ≤ ‖P_K v‖² ‖a‖²`. -/
theorem inner_sq_le_norm_sq_starProjection_mul {K : Submodule ℝ V} [FiniteDimensional ℝ K]
    {a : V} (ha : a ∈ K) (v : V) :
    ⟪v, a⟫ ^ 2 ≤ ‖K.starProjection v‖ ^ 2 * ‖a‖ ^ 2 := by
  have h : ⟪v, a⟫ = ⟪K.starProjection v, a⟫ := by
    rw [K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr ha]
  rw [h, ← mul_pow]
  exact sq_le_sq' (neg_le_of_abs_le (abs_real_inner_le_norm _ _))
    (le_of_abs_le (abs_real_inner_le_norm _ _))

/-! ### Horizontal packets -/

/-- A finite horizontal packet: real points of multiplicity at least two (`f₂`, weights `m₂`),
horizontally simple real points `fH`, mixed real points `fM`, and conjugate pairs `(g, h)` with
multiplicities `mP`. -/
structure HorizontalPacket (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ι₂ ιH ιM ιP : Type*) where
  /-- vectors of the real points of multiplicity at least two -/
  f₂ : ι₂ → V
  /-- their multiplicities -/
  m₂ : ι₂ → ℝ
  /-- vectors of the horizontally simple real points -/
  fH : ιH → V
  /-- vectors of the mixed real points -/
  fM : ιM → V
  /-- even parts `g_z = (f_z + f_z̄)/2` of the conjugate pairs -/
  g : ιP → V
  /-- odd parts `h_z = (f_z − f_z̄)/(2i)` of the conjugate pairs -/
  h : ιP → V
  /-- multiplicities of the conjugate pairs -/
  mP : ιP → ℝ

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP)

/-- The normalisations of Lamzouri's vectors: unit real vectors, multiplicities `≥ 2` for the
multiple real points and `≥ 1` for the pairs, and `‖g‖² − ‖h‖² = 1`. -/
structure Admissible : Prop where
  norm_f₂ : ∀ i, ‖P.f₂ i‖ = 1
  two_le_m₂ : ∀ i, 2 ≤ P.m₂ i
  norm_fH : ∀ i, ‖P.fH i‖ = 1
  norm_fM : ∀ i, ‖P.fM i‖ = 1
  one_le_mP : ∀ p, 1 ≤ P.mP p
  norm_sq_g_sub_norm_sq_h : ∀ p, ‖P.g p‖ ^ 2 - ‖P.h p‖ ^ 2 = 1

/-- All vectors of the packet. -/
def vec : ι₂ ⊕ ιH ⊕ ιM ⊕ ιP ⊕ ιP → V :=
  Sum.elim P.f₂ (Sum.elim P.fH (Sum.elim P.fM (Sum.elim P.g P.h)))

/-- Their weights: `m`, `1`, `1`, `2m`, `−2m`. -/
def wt : ι₂ ⊕ ιH ⊕ ιM ⊕ ιP ⊕ ιP → ℝ :=
  Sum.elim P.m₂ (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1)
    (Sum.elim (fun p => 2 * P.mP p) (fun p => -(2 * P.mP p)))))

/-- The energy `Σ_{k,l} c_k c_l ⟪w_k, w_l⟫²` (Lamzouri's `Σ_{z,s} K(z − s)²`). -/
def energy : ℝ := ∑ k, ∑ l, P.wt k * P.wt l * ⟪P.vec k, P.vec l⟫ ^ 2

/-- The mass `Σ_k c_k ‖w_k‖²` (the number of points, see `mass_eq`). -/
def mass : ℝ := ∑ k, P.wt k * ‖P.vec k‖ ^ 2

/-- The diagonal form `ψ ↦ Σ_k c_k ⟪w_k, ψ⟫²`. -/
def diagForm (ψ : V) : ℝ := ∑ k, P.wt k * ⟪P.vec k, ψ⟫ ^ 2

/-- The absorbing span `A = span(f₂, g)`. -/
def absorbing : Submodule ℝ V := Submodule.span ℝ (Set.range (Sum.elim P.f₂ P.g))

/-- `C = A ⊔ span fH`. -/
def hsSpan : Submodule ℝ V := P.absorbing ⊔ Submodule.span ℝ (Set.range P.fH)

/-- `B = C ⊔ span fM`, the span of all positive vectors. -/
def positiveSpan : Submodule ℝ V := P.hsSpan ⊔ Submodule.span ℝ (Set.range P.fM)

/-- `W = B ⊔ span h`, the span of all vectors. -/
def fullSpan : Submodule ℝ V := P.positiveSpan ⊔ Submodule.span ℝ (Set.range P.h)

instance : FiniteDimensional ℝ P.absorbing :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

instance : FiniteDimensional ℝ P.hsSpan := by
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range P.fH)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  unfold hsSpan; infer_instance

instance : FiniteDimensional ℝ P.positiveSpan := by
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range P.fM)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  unfold positiveSpan; infer_instance

instance : FiniteDimensional ℝ P.fullSpan := by
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range P.h)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  unfold fullSpan; infer_instance

/-- The overlap `T = Σ_{x ∈ M} ‖P_A f_x‖²` of the mixed points with the absorbing span. -/
def mixedOverlap : ℝ := ∑ x, ‖P.absorbing.starProjection (P.fM x)‖ ^ 2

/-- The unabsorbed negative mass `Λ = Σ_p m_p (‖P_{A^⊥} h_p‖² + ‖P_{B^⊥} h_p‖²)`. -/
def leakage : ℝ := ∑ p, P.mP p *
  (‖P.absorbingᗮ.starProjection (P.h p)‖ ^ 2 + ‖P.positiveSpanᗮ.starProjection (P.h p)‖ ^ 2)

theorem sum_wt_mul (F : V → ℝ) :
    ∑ k, P.wt k * F (P.vec k) = ∑ i, P.m₂ i * F (P.f₂ i) + ∑ i, F (P.fH i) + ∑ i, F (P.fM i)
      + ∑ p, 2 * P.mP p * F (P.g p) - ∑ p, 2 * P.mP p * F (P.h p) := by
  simp only [wt, vec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul,
    Finset.sum_neg_distrib]
  ring

/-- The mass is the number of points counted with multiplicity. -/
theorem mass_eq (hP : P.Admissible) :
    P.mass = ∑ i, P.m₂ i + Fintype.card ιH + Fintype.card ιM + 2 * ∑ p, P.mP p := by
  have h := P.sum_wt_mul (fun v => ‖v‖ ^ 2)
  simp only [mass] at h ⊢
  rw [h]
  simp only [hP.norm_f₂, hP.norm_fH, hP.norm_fM, one_pow, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have : ∑ p, 2 * P.mP p * ‖P.g p‖ ^ 2 - ∑ p, 2 * P.mP p * ‖P.h p‖ ^ 2 = 2 * ∑ p, P.mP p := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have := hP.norm_sq_g_sub_norm_sq_h p
    linear_combination 2 * P.mP p * this
  linarith

theorem sum_diagForm_stdOrthonormalBasis (K : Submodule ℝ V) [FiniteDimensional ℝ K] :
    ∑ j, P.diagForm ((stdOrthonormalBasis ℝ K) j : V) =
      ∑ k, P.wt k * ‖K.starProjection (P.vec k)‖ ^ 2 := by
  simp only [diagForm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, sum_sq_inner_stdOrthonormalBasis]

theorem f₂_mem_absorbing (i : ι₂) : P.f₂ i ∈ P.absorbing :=
  Submodule.subset_span ⟨Sum.inl i, rfl⟩

theorem g_mem_absorbing (p : ιP) : P.g p ∈ P.absorbing :=
  Submodule.subset_span ⟨Sum.inr p, rfl⟩

theorem absorbing_le_hsSpan : P.absorbing ≤ P.hsSpan := le_sup_left

theorem fH_mem_hsSpan (i : ιH) : P.fH i ∈ P.hsSpan :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

theorem hsSpan_le_positiveSpan : P.hsSpan ≤ P.positiveSpan := le_sup_left

theorem fM_mem_positiveSpan (i : ιM) : P.fM i ∈ P.positiveSpan :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

theorem positiveSpan_le_fullSpan : P.positiveSpan ≤ P.fullSpan := le_sup_left

theorem h_mem_fullSpan (p : ιP) : P.h p ∈ P.fullSpan :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨p, rfl⟩)

theorem vec_mem_fullSpan (k : ι₂ ⊕ ιH ⊕ ιM ⊕ ιP ⊕ ιP) : P.vec k ∈ P.fullSpan := by
  have hB : ∀ {v}, v ∈ P.positiveSpan → v ∈ P.fullSpan := fun hv => P.positiveSpan_le_fullSpan hv
  have hC : ∀ {v}, v ∈ P.hsSpan → v ∈ P.fullSpan := fun hv => hB (P.hsSpan_le_positiveSpan hv)
  have hA : ∀ {v}, v ∈ P.absorbing → v ∈ P.fullSpan := fun hv => hC (P.absorbing_le_hsSpan hv)
  rcases k with i | i | i | p | p
  · exact hA (P.f₂_mem_absorbing i)
  · exact hC (P.fH_mem_hsSpan i)
  · exact hB (P.fM_mem_positiveSpan i)
  · exact hA (P.g_mem_absorbing p)
  · exact P.h_mem_fullSpan p

theorem finrank_absorbing_le :
    finrank ℝ P.absorbing ≤ Fintype.card ι₂ + Fintype.card ιP := by
  have h := finrank_range_le_card (R := ℝ) (Sum.elim P.f₂ P.g)
  rw [Fintype.card_sum] at h
  exact h

theorem finrank_hsSpan_inf_le :
    finrank ℝ (P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V) ≤ Fintype.card ιH := by
  have h1 := Submodule.finrank_add_inf_finrank_orthogonal P.absorbing_le_hsSpan
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range P.fH)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank P.absorbing
    (Submodule.span ℝ (Set.range P.fH))
  have h3 := finrank_range_le_card (R := ℝ) P.fH
  change finrank ℝ (Submodule.span ℝ (Set.range P.fH)) ≤ _ at h3
  change finrank ℝ P.hsSpan ≤ _ at h2
  omega

theorem finrank_positiveSpan_inf_le :
    finrank ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V) ≤ Fintype.card ιM := by
  have h1 := Submodule.finrank_add_inf_finrank_orthogonal P.hsSpan_le_positiveSpan
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range P.fM)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank P.hsSpan
    (Submodule.span ℝ (Set.range P.fM))
  have h3 := finrank_range_le_card (R := ℝ) P.fM
  change finrank ℝ (Submodule.span ℝ (Set.range P.fM)) ≤ _ at h3
  change finrank ℝ P.positiveSpan ≤ _ at h2
  omega

/-- The frame: orthonormal bases of `A`, `Aᗮ ⊓ C`, `Cᗮ ⊓ B` and `Bᗮ ⊓ W`. -/
def frame : Fin (finrank ℝ P.absorbing) ⊕ Fin (finrank ℝ (P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V)) ⊕
    Fin (finrank ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) ⊕
    Fin (finrank ℝ (P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V)) → V :=
  Sum.elim (fun j => ((stdOrthonormalBasis ℝ P.absorbing) j : V))
    (Sum.elim (fun j => ((stdOrthonormalBasis ℝ (P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V)) j : V))
      (Sum.elim (fun j => ((stdOrthonormalBasis ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V))
        (fun j => ((stdOrthonormalBasis ℝ (P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V)) j : V))))

/-- The frame reproduces inner products on `W`. -/
theorem frame_parseval {u : V} (hu : u ∈ P.fullSpan) (v : V) :
    ∑ s, ⟪u, P.frame s⟫ * ⟪v, P.frame s⟫ = ⟪u, v⟫ := by
  simp only [frame, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    sum_inner_mul_inner_stdOrthonormalBasis]
  rw [← inner_add_left, ← inner_add_left, ← inner_add_left, ← add_assoc,
    ← starProjection_eq_add_starProjection_inf_orthogonal P.absorbing_le_hsSpan, ← add_assoc,
    ← starProjection_eq_add_starProjection_inf_orthogonal P.hsSpan_le_positiveSpan,
    ← starProjection_eq_add_starProjection_inf_orthogonal P.positiveSpan_le_fullSpan,
    P.fullSpan.starProjection_eq_self_iff.mpr hu]

theorem norm_sq_split {v : V} (hv : v ∈ P.fullSpan) :
    ‖P.absorbing.starProjection v‖ ^ 2
      + ‖(P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V).starProjection v‖ ^ 2
      + ‖(P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V).starProjection v‖ ^ 2
      + ‖(P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V).starProjection v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := P.frame_parseval hv v
  simp only [frame, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← sq,
    sum_sq_inner_stdOrthonormalBasis] at h
  rw [real_inner_self_eq_norm_sq] at h
  linarith

theorem diagForm_eq (ψ : V) :
    P.diagForm ψ = ∑ i, P.m₂ i * ⟪P.f₂ i, ψ⟫ ^ 2 + ∑ i, ⟪P.fH i, ψ⟫ ^ 2 + ∑ i, ⟪P.fM i, ψ⟫ ^ 2
      + ∑ p, 2 * P.mP p * ⟪P.g p, ψ⟫ ^ 2 - ∑ p, 2 * P.mP p * ⟪P.h p, ψ⟫ ^ 2 :=
  P.sum_wt_mul (fun v => ⟪v, ψ⟫ ^ 2)

theorem diagForm_le_of_mem_orthogonal_hsSpan (hP : P.Admissible) {ψ : V}
    (hψ : ψ ∈ P.hsSpanᗮ) : P.diagForm ψ ≤ ∑ i, ⟪P.fM i, ψ⟫ ^ 2 := by
  rw [P.diagForm_eq]
  have h1 : ∀ i, ⟪P.f₂ i, ψ⟫ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal (P.absorbing_le_hsSpan (P.f₂_mem_absorbing i)) hψ
  have h2 : ∀ i, ⟪P.fH i, ψ⟫ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal (P.fH_mem_hsSpan i) hψ
  have h3 : ∀ p, ⟪P.g p, ψ⟫ = 0 := fun p =>
    Submodule.inner_right_of_mem_orthogonal (P.absorbing_le_hsSpan (P.g_mem_absorbing p)) hψ
  simp only [h1, h2, h3, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  have : 0 ≤ ∑ p, 2 * P.mP p * ⟪P.h p, ψ⟫ ^ 2 := Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg zero_le_two (le_trans zero_le_one (hP.one_le_mP p))) (sq_nonneg _)
  linarith

theorem diagForm_eq_of_mem_orthogonal_positiveSpan {ψ : V} (hψ : ψ ∈ P.positiveSpanᗮ) :
    P.diagForm ψ = -∑ p, 2 * P.mP p * ⟪P.h p, ψ⟫ ^ 2 := by
  rw [P.diagForm_eq]
  have hC : ∀ {v}, v ∈ P.hsSpan → ⟪v, ψ⟫ = 0 := fun hv =>
    Submodule.inner_right_of_mem_orthogonal (P.hsSpan_le_positiveSpan hv) hψ
  have h1 : ∀ i, ⟪P.f₂ i, ψ⟫ = 0 := fun i => hC (P.absorbing_le_hsSpan (P.f₂_mem_absorbing i))
  have h2 : ∀ i, ⟪P.fH i, ψ⟫ = 0 := fun i => hC (P.fH_mem_hsSpan i)
  have h3 : ∀ p, ⟪P.g p, ψ⟫ = 0 := fun p => hC (P.absorbing_le_hsSpan (P.g_mem_absorbing p))
  have h4 : ∀ i, ⟪P.fM i, ψ⟫ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal (P.fM_mem_positiveSpan i) hψ
  simp only [h1, h2, h3, h4, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Finset.sum_const_zero, zero_add, zero_sub]

/-- On `W`, the projection onto `Bᗮ ⊓ W` is the projection onto `Bᗮ`. -/
theorem starProjection_inf_fullSpan {v : V} (hv : v ∈ P.fullSpan) :
    (P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V).starProjection v =
      P.positiveSpanᗮ.starProjection v := by
  have h := starProjection_eq_add_starProjection_inf_orthogonal P.positiveSpan_le_fullSpan v
  rw [P.fullSpan.starProjection_eq_self_iff.mpr hv] at h
  rw [Submodule.starProjection_orthogonal_val, eq_sub_iff_add_eq, add_comm]
  exact h.symm

/-- **The absorbing range** carries at least `2 dim A + T + 2 Σ m ‖P_{A^⊥} h‖²`. -/
theorem absorbing_sum (hP : P.Admissible) :
    2 * (Fintype.card ι₂ + Fintype.card ιP : ℝ) + P.mixedOverlap
      + 2 * ∑ p, P.mP p * ‖P.absorbingᗮ.starProjection (P.h p)‖ ^ 2
      ≤ ∑ j, P.diagForm ((stdOrthonormalBasis ℝ P.absorbing) j : V) := by
  rw [P.sum_diagForm_stdOrthonormalBasis, P.sum_wt_mul (fun v => ‖P.absorbing.starProjection v‖ ^ 2)]
  have e₂ : ∀ i, P.absorbing.starProjection (P.f₂ i) = P.f₂ i := fun i =>
    P.absorbing.starProjection_eq_self_iff.mpr (P.f₂_mem_absorbing i)
  have eg : ∀ p, P.absorbing.starProjection (P.g p) = P.g p := fun p =>
    P.absorbing.starProjection_eq_self_iff.mpr (P.g_mem_absorbing p)
  have eh : ∀ p, ‖P.absorbing.starProjection (P.h p)‖ ^ 2 =
      ‖P.h p‖ ^ 2 - ‖P.absorbingᗮ.starProjection (P.h p)‖ ^ 2 := fun p => by
    have := Submodule.norm_sq_eq_add_norm_sq_starProjection (P.h p) P.absorbing
    linarith
  simp only [e₂, eg, eh, hP.norm_f₂, one_pow, mul_one]
  have hm₂ : 2 * (Fintype.card ι₂ : ℝ) ≤ ∑ i, P.m₂ i := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hP.two_le_m₂ i
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using this
  have hH : 0 ≤ ∑ i, ‖P.absorbing.starProjection (P.fH i)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpair : ∑ p, 2 * P.mP p * ‖P.g p‖ ^ 2
      - ∑ p, 2 * P.mP p * (‖P.h p‖ ^ 2 - ‖P.absorbingᗮ.starProjection (P.h p)‖ ^ 2)
      = 2 * ∑ p, P.mP p + 2 * ∑ p, P.mP p * ‖P.absorbingᗮ.starProjection (P.h p)‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have := hP.norm_sq_g_sub_norm_sq_h p
    linear_combination 2 * P.mP p * this
  have hmP : (Fintype.card ιP : ℝ) ≤ ∑ p, P.mP p := by
    have := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hP.one_le_mP p
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  simp only [mixedOverlap]
  linarith

/-- **The mixed range** carries at most `#M − T`. -/
theorem mixed_range_sum_le (hP : P.Admissible) :
    ∑ j, P.diagForm ((stdOrthonormalBasis ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V)
      ≤ Fintype.card ιM - P.mixedOverlap := by
  set K₃ : Submodule ℝ V := P.hsSpanᗮ ⊓ P.positiveSpan
  calc ∑ j, P.diagForm ((stdOrthonormalBasis ℝ K₃) j : V)
        ≤ ∑ j, ∑ i, ⟪P.fM i, ((stdOrthonormalBasis ℝ K₃) j : V)⟫ ^ 2 :=
        Finset.sum_le_sum fun j _ => P.diagForm_le_of_mem_orthogonal_hsSpan hP
          (Submodule.mem_inf.mp ((stdOrthonormalBasis ℝ K₃) j).2).1
    _ = ∑ i, ‖K₃.starProjection (P.fM i)‖ ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => sum_sq_inner_stdOrthonormalBasis K₃ (P.fM i)
    _ ≤ ∑ i, (1 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hv := P.vec_mem_fullSpan (Sum.inr (Sum.inr (Sum.inl i)))
        simp only [vec, Sum.elim_inr, Sum.elim_inl] at hv
        have h := P.norm_sq_split hv
        rw [hP.norm_fM i] at h
        have := sq_nonneg ‖(P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V).starProjection (P.fM i)‖
        have := sq_nonneg ‖(P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V).starProjection (P.fM i)‖
        linarith
    _ = Fintype.card ιM - P.mixedOverlap := by
        simp [Finset.sum_sub_distrib, mixedOverlap]

/-- **The negative range** gains `4 Σ m ‖P_{B^⊥} h‖²`. -/
theorem negative_range_bound :
    2 * ∑ j, P.diagForm ((stdOrthonormalBasis ℝ (P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V)) j : V)
      + 4 * ∑ p, P.mP p * ‖P.positiveSpanᗮ.starProjection (P.h p)‖ ^ 2
      ≤ ∑ j, P.diagForm
        ((stdOrthonormalBasis ℝ (P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V)) j : V) ^ 2 := by
  set K₄ : Submodule ℝ V := P.positiveSpanᗮ ⊓ P.fullSpan
  set b := stdOrthonormalBasis ℝ K₄
  have e : ∀ j, P.diagForm (b j) = -∑ p, 2 * P.mP p * ⟪P.h p, (b j : V)⟫ ^ 2 :=
    fun j => P.diagForm_eq_of_mem_orthogonal_positiveSpan (Submodule.mem_inf.mp (b j).2).1
  have hsum : ∑ j, ∑ p, 2 * P.mP p * ⟪P.h p, (b j : V)⟫ ^ 2
      = 2 * ∑ p, P.mP p * ‖P.positiveSpanᗮ.starProjection (P.h p)‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.mul_sum, sum_sq_inner_stdOrthonormalBasis,
      P.starProjection_inf_fullSpan (P.h_mem_fullSpan p)]
    ring
  have hpt : ∀ j, 2 * P.diagForm (b j) + 2 * ∑ p, 2 * P.mP p * ⟪P.h p, (b j : V)⟫ ^ 2
      ≤ P.diagForm (b j) ^ 2 := fun j => by
    rw [e j]; nlinarith [sq_nonneg (∑ p, 2 * P.mP p * ⟪P.h p, (b j : V)⟫ ^ 2)]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpt j
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum] at h
  linarith

theorem mass_eq_frame_sum : ∑ s, P.diagForm (P.frame s) = P.mass := by
  simp only [diagForm, mass]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have := P.frame_parseval (P.vec_mem_fullSpan k) (P.vec k)
  simp only [← sq] at this
  rw [this, real_inner_self_eq_norm_sq]

/-- The four-range estimate, with the mixed range kept as free data. -/
theorem exists_mixed_range (hP : P.Admissible) :
    ∃ (d : ℕ) (α : Fin d → ℝ), (d : ℝ) ≤ Fintype.card ιM ∧
      ∑ j, α j ≤ Fintype.card ιM - P.mixedOverlap ∧
      2 * P.mass - Fintype.card ιH + 2 * P.mixedOverlap + 4 * P.leakage
        + (∑ j, α j ^ 2 - 2 * ∑ j, α j) ≤ P.energy := by
  refine ⟨finrank ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V),
    fun j => P.diagForm ((stdOrthonormalBasis ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V),
    ?_, P.mixed_range_sum_le hP, ?_⟩
  · exact_mod_cast P.finrank_positiveSpan_inf_le
  have hE : ∑ s, P.diagForm (P.frame s) ^ 2 ≤ P.energy :=
    sum_sq_diag_le_energy P.frame P.vec
      (fun k l => P.frame_parseval (P.vec_mem_fullSpan k) (P.vec l)) P.wt
  have hM := P.mass_eq_frame_sum
  simp only [frame, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hE hM
  have hA1 := P.absorbing_sum hP
  have hq₁ := sum_sq_ge_of_center
    (fun j => P.diagForm ((stdOrthonormalBasis ℝ P.absorbing) j : V)) 2
  have hd₁ : (finrank ℝ P.absorbing : ℝ) ≤ Fintype.card ι₂ + Fintype.card ιP := by
    exact_mod_cast P.finrank_absorbing_le
  have hq₂ := sum_sq_ge_of_center
    (fun j => P.diagForm ((stdOrthonormalBasis ℝ (P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V)) j : V)) 1
  have hd₂ : (finrank ℝ (P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V) : ℝ) ≤ Fintype.card ιH := by
    exact_mod_cast P.finrank_hsSpan_inf_le
  have hq₄ := P.negative_range_bound
  have hleak : P.leakage = ∑ p, P.mP p * ‖P.absorbingᗮ.starProjection (P.h p)‖ ^ 2
      + ∑ p, P.mP p * ‖P.positiveSpanᗮ.starProjection (P.h p)‖ ^ 2 := by
    simp only [leakage, mul_add, Finset.sum_add_distrib]
  simp only [one_pow, one_mul, mul_one] at hq₂
  norm_num at hq₁
  rw [hleak]
  linarith

theorem mixedOverlap_nonneg : 0 ≤ P.mixedOverlap :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem mixedOverlap_le (hP : P.Admissible) : P.mixedOverlap ≤ Fintype.card ιM := by
  have h : ∀ i, ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 ≤ 1 := fun i => by
    have h1 := Submodule.norm_starProjection_apply_le P.absorbing (P.fM i)
    rw [hP.norm_fM i] at h1
    have h0 := norm_nonneg (P.absorbing.starProjection (P.fM i))
    nlinarith
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  simpa [mixedOverlap, Finset.sum_const, Finset.card_univ] using this

theorem leakage_nonneg (hP : P.Admissible) : 0 ≤ P.leakage :=
  Finset.sum_nonneg fun p _ => mul_nonneg (le_trans zero_le_one (hP.one_le_mP p))
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **Horizontal Lamzouri inequality.**
`2N − #H − #M + 2T + 4Λ ≤ E`. -/
theorem energy_lower_bound (hP : P.Admissible) :
    2 * P.mass - Fintype.card ιH - Fintype.card ιM + 2 * P.mixedOverlap + 4 * P.leakage
      ≤ P.energy := by
  obtain ⟨d, α, hd, -, h⟩ := P.exists_mixed_range hP
  have h1 := sum_sq_ge_of_center α 1
  simp only [one_pow, one_mul, mul_one] at h1
  linarith

/-- **Sharp horizontal Lamzouri inequality.**
`T² ≤ #M · (E − (2N − #H − #M + 2T + 4Λ))`. -/
theorem mixedOverlap_sq_le (hP : P.Admissible) :
    P.mixedOverlap ^ 2 ≤ Fintype.card ιM * (P.energy -
      (2 * P.mass - Fintype.card ιH - Fintype.card ιM + 2 * P.mixedOverlap + 4 * P.leakage)) := by
  obtain ⟨d, α, hd, hs, h⟩ := P.exists_mixed_range hP
  have hsharp := sq_le_card_mul_of_sum_le α hd P.mixedOverlap_nonneg (P.mixedOverlap_le hP) hs
  have hn : (0 : ℝ) ≤ Fintype.card ιM := Nat.cast_nonneg _
  calc P.mixedOverlap ^ 2 ≤ Fintype.card ιM * (∑ j, α j ^ 2 - 2 * ∑ j, α j + Fintype.card ιM) :=
        hsharp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hn

/-- Lamzouri's simple-real inequality `#(simple real) ≥ 2N − E`, the case that ignores
horizontal structure. -/
theorem lamzouri_inequality (hP : P.Admissible) :
    2 * P.mass - P.energy ≤ Fintype.card ιH + Fintype.card ιM := by
  have := P.energy_lower_bound hP
  have := P.mixedOverlap_nonneg
  have := P.leakage_nonneg hP
  linarith

/-- The horizontally simple count misses Lamzouri's bound by at most `#M − 2T − 4Λ`. -/
theorem card_hs_lower_bound (hP : P.Admissible) :
    2 * P.mass - P.energy - (Fintype.card ιM - 2 * P.mixedOverlap - 4 * P.leakage)
      ≤ Fintype.card ιH := by
  have := P.energy_lower_bound hP
  linarith

/-- **Horizontal criterion.** If `#M² ≤ #M (2T + 4Λ) + T²`, the horizontally simple points
alone satisfy Lamzouri's bound `#H ≥ 2N − E`. -/
theorem card_hs_ge_of_overlap (hP : P.Admissible)
    (hover : (Fintype.card ιM : ℝ) ^ 2
      ≤ Fintype.card ιM * (2 * P.mixedOverlap + 4 * P.leakage) + P.mixedOverlap ^ 2) :
    2 * P.mass - P.energy ≤ Fintype.card ιH := by
  set n : ℝ := (Fintype.card ιM : ℝ) with hn_def
  set X := P.energy - (2 * P.mass - Fintype.card ιH - n + 2 * P.mixedOverlap + 4 * P.leakage)
  have hsharp : P.mixedOverlap ^ 2 ≤ n * X := P.mixedOverlap_sq_le hP
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hkey : n * (n - 2 * P.mixedOverlap - 4 * P.leakage) ≤ n * X := by nlinarith
  rcases hn.lt_or_eq with hpos | hzero
  · have := le_of_mul_le_mul_left hkey hpos
    simp only [X] at this
    linarith
  · have hc : (Fintype.card ιM : ℝ) = 0 := hzero.symm
    have hT : P.mixedOverlap = 0 := by
      have h1 := P.mixedOverlap_nonneg
      have h2 := P.mixedOverlap_le hP
      rw [hc] at h2
      linarith
    have hl := P.leakage_nonneg hP
    have hE := P.energy_lower_bound hP
    rw [hc, hT] at hE
    linarith

/-- If every mixed point has overlap at least `√2 − 1` with the absorbing span, the
horizontally simple points alone satisfy Lamzouri's bound. -/
theorem card_hs_ge_of_overlap_ge (hP : P.Admissible)
    (hover : ∀ i, Real.sqrt 2 - 1 ≤ ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) :
    2 * P.mass - P.energy ≤ Fintype.card ιH := by
  refine P.card_hs_ge_of_overlap hP ?_
  have hT : (Real.sqrt 2 - 1) * (Fintype.card ιM : ℝ) ≤ P.mixedOverlap := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hover i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    simp only [mixedOverlap]
    linarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hn : (0 : ℝ) ≤ Fintype.card ιM := Nat.cast_nonneg _
  have hl := P.leakage_nonneg hP
  have hc0 : 0 ≤ (Real.sqrt 2 - 1) * (Fintype.card ιM : ℝ) := mul_nonneg (by linarith) hn
  have hsq : ((Real.sqrt 2 - 1) * (Fintype.card ιM : ℝ)) ^ 2 ≤ P.mixedOverlap ^ 2 :=
    pow_le_pow_left₀ hc0 hT 2
  have key : (Fintype.card ιM : ℝ) ^ 2 ≤ (Fintype.card ιM : ℝ) *
      (2 * ((Real.sqrt 2 - 1) * (Fintype.card ιM : ℝ))) +
        ((Real.sqrt 2 - 1) * (Fintype.card ιM : ℝ)) ^ 2 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hT hn, mul_nonneg hn hl]

/-- A mixed point's own pair vector lies in the absorbing span:
`T ≥ Σ_x ⟪f_x, g_{σ(x)}⟫² / ‖g_{σ(x)}‖²` for every choice of pairs `σ`. -/
theorem mixedOverlap_ge_ownPair (σ : ιM → ιP) :
    ∑ i, ⟪P.fM i, P.g (σ i)⟫ ^ 2 / ‖P.g (σ i)‖ ^ 2 ≤ P.mixedOverlap := by
  refine Finset.sum_le_sum fun i _ => ?_
  have h := inner_sq_le_norm_sq_starProjection_mul (P.g_mem_absorbing (σ i)) (P.fM i)
  rcases (sq_nonneg ‖P.g (σ i)‖).lt_or_eq with hpos | hzero
  · rw [div_le_iff₀ hpos]; exact h
  · rw [← hzero, div_zero]; exact sq_nonneg _

end HorizontalPacket

end

end GaloisForLFunctions.HilbertMetric
