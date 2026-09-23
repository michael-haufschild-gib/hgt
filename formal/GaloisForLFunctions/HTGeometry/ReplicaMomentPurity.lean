import GaloisForLFunctions.HTGeometry.SymmetricReplicaProjector

/-!
# The moment of a finitely supported target law and its purity barrier

The replica moment of a law supported on finitely many unit targets is the corresponding convex
combination of replica projectors.  It is Hermitian, has trace one, and is carried by the symmetric
replica projector, so the projection-form purity barrier applies to it verbatim.

Its purity is a law-weighted double sum of squared replica overlaps.  Every term is non-negative
and the diagonal terms are the squared weights, so the purity is at least the squared mass of the
law, hence at least the reciprocal of the number of supported targets.  Subtracting the normalized
symmetric projector leaves an energy of at least `1/N - 1/h`; in the capacity regime `N < a^r h`
that energy exceeds `(1-a^r)/N`.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Moment

variable {α : Type*} [Fintype α] [DecidableEq α] {C : Type*} [Fintype C]

/-- **`(20)`.**  The replica moment of a finitely supported law on pure targets. -/
def replicaMoment (r : ℕ) (w : C → ℝ) (target : C → α → ℂ) :
    Matrix (Fin r → α) (Fin r → α) ℂ :=
  Matrix.of fun x y => ∑ c, (w c : ℂ) *
    (finitePureTensorPower r (target c) x *
      (starRingEnd ℂ) (finitePureTensorPower r (target c) y))

theorem replicaMoment_apply (r : ℕ) (w : C → ℝ) (target : C → α → ℂ)
    (x y : Fin r → α) :
    replicaMoment r w target x y = ∑ c, (w c : ℂ) *
      (finitePureTensorPower r (target c) x *
        (starRingEnd ℂ) (finitePureTensorPower r (target c) y)) := rfl

theorem replicaMoment_conjTranspose (r : ℕ) (w : C → ℝ) (target : C → α → ℂ) :
    (replicaMoment r w target)ᴴ = replicaMoment r w target := by
  funext x y
  rw [Matrix.conjTranspose_apply, replicaMoment_apply, replicaMoment_apply, RCLike.star_def,
    map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- The moment is carried by the symmetric replica projector. -/
theorem symReplicaProjection_mul_replicaMoment (r : ℕ) (w : C → ℝ) (target : C → α → ℂ) :
    symReplicaProjection (α := α) r * replicaMoment r w target = replicaMoment r w target := by
  funext x y
  rw [Matrix.mul_apply, replicaMoment_apply]
  have hrow : ∀ c : C, (∑ z : Fin r → α, symReplicaProjection (α := α) r x z *
      finitePureTensorPower r (target c) z) = finitePureTensorPower r (target c) x := by
    intro c
    have h := congrFun (symReplicaProjection_mulVec_pure r (target c)) x
    simpa [Matrix.mulVec, dotProduct] using h
  calc (∑ z : Fin r → α, symReplicaProjection (α := α) r x z * replicaMoment r w target z y)
      = ∑ z : Fin r → α, ∑ c, symReplicaProjection (α := α) r x z * ((w c : ℂ) *
          (finitePureTensorPower r (target c) z *
            (starRingEnd ℂ) (finitePureTensorPower r (target c) y))) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [replicaMoment_apply, Finset.mul_sum]
    _ = ∑ c, ∑ z : Fin r → α, symReplicaProjection (α := α) r x z * ((w c : ℂ) *
          (finitePureTensorPower r (target c) z *
            (starRingEnd ℂ) (finitePureTensorPower r (target c) y))) := Finset.sum_comm
    _ = ∑ c, (w c : ℂ) * (finitePureTensorPower r (target c) x *
          (starRingEnd ℂ) (finitePureTensorPower r (target c) y)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hfac : ∀ z : Fin r → α, symReplicaProjection (α := α) r x z * ((w c : ℂ) *
            (finitePureTensorPower r (target c) z *
              (starRingEnd ℂ) (finitePureTensorPower r (target c) y)))
            = ((w c : ℂ) * (starRingEnd ℂ) (finitePureTensorPower r (target c) y)) *
              (symReplicaProjection (α := α) r x z *
                finitePureTensorPower r (target c) z) := by
          intro z; ring
        rw [Finset.sum_congr rfl fun z _ => hfac z, ← Finset.mul_sum, hrow c]
        ring

/-- The moment of a probability law on unit targets has trace one. -/
theorem replicaMoment_trace (r : ℕ) (w : C → ℝ) (target : C → α → ℂ)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (hsum : ∑ c, w c = 1) :
    (replicaMoment r w target).trace = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, replicaMoment_apply]
  rw [Finset.sum_comm]
  have hc : ∀ c : C, (∑ x : Fin r → α, (w c : ℂ) *
      (finitePureTensorPower r (target c) x *
        (starRingEnd ℂ) (finitePureTensorPower r (target c) x))) = (w c : ℂ) := by
    intro c
    rw [← Finset.mul_sum]
    have hnorm : (∑ x : Fin r → α, finitePureTensorPower r (target c) x *
        (starRingEnd ℂ) (finitePureTensorPower r (target c) x))
        = finiteComplexInner (finitePureTensorPower r (target c))
            (finitePureTensorPower r (target c)) := by
      rw [finiteComplexInner]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hnorm, finiteComplexInner_pureTensorPower, hunit c, one_pow, mul_one]
  rw [Finset.sum_congr rfl fun c _ => hc c, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

/-- The purity of the moment is the law-weighted double sum of squared replica overlaps. -/
theorem hsNormSq_replicaMoment (r : ℕ) (w : C → ℝ) (target : C → α → ℂ) :
    hsNormSq (replicaMoment r w target)
      = ∑ c, ∑ c', w c * w c' *
          ‖finiteComplexInner (target c) (target c') ^ r‖ ^ (2 : ℕ) := by
  classical
  have hI : ∀ c c' : C, (∑ x : Fin r → α,
      (starRingEnd ℂ) (finitePureTensorPower r (target c) x) *
        finitePureTensorPower r (target c') x)
      = finiteComplexInner (target c) (target c') ^ r := by
    intro c c'
    have h := finiteComplexInner_pureTensorPower r (target c) (target c')
    rw [finiteComplexInner] at h
    exact h
  have hJ : ∀ c c' : C, (∑ y : Fin r → α, finitePureTensorPower r (target c) y *
      (starRingEnd ℂ) (finitePureTensorPower r (target c') y))
      = (starRingEnd ℂ) (finiteComplexInner (target c) (target c') ^ r) := by
    intro c c'
    rw [← hI c c', map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, Complex.conj_conj]
  have hkey : ((hsNormSq (replicaMoment r w target) : ℝ) : ℂ)
      = ∑ c, ∑ c', ((w c * w c' *
          ‖finiteComplexInner (target c) (target c') ^ r‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [hsNormSq_eq_sum_star]
    have hexpand : ∀ x y : Fin r → α,
        star (replicaMoment r w target x y) * replicaMoment r w target x y
          = ∑ c, ∑ c', ((w c : ℂ) * (w c' : ℂ)) *
              (((starRingEnd ℂ) (finitePureTensorPower r (target c) x) *
                  finitePureTensorPower r (target c') x) *
                (finitePureTensorPower r (target c) y *
                  (starRingEnd ℂ) (finitePureTensorPower r (target c') y))) := by
      intro x y
      have hstar : star (replicaMoment r w target x y)
          = ∑ c, (w c : ℂ) * ((starRingEnd ℂ) (finitePureTensorPower r (target c) x) *
              finitePureTensorPower r (target c) y) := by
        rw [replicaMoment_apply, RCLike.star_def, map_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      rw [hstar, replicaMoment_apply, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => by ring
    have hx : ∀ y : Fin r → α, (∑ x : Fin r → α,
        star (replicaMoment r w target x y) * replicaMoment r w target x y)
        = ∑ c, ∑ c', ((w c : ℂ) * (w c' : ℂ)) *
            ((∑ x : Fin r → α, (starRingEnd ℂ) (finitePureTensorPower r (target c) x) *
                finitePureTensorPower r (target c') x) *
              (finitePureTensorPower r (target c) y *
                (starRingEnd ℂ) (finitePureTensorPower r (target c') y))) := by
      intro y
      rw [Finset.sum_congr rfl fun x _ => hexpand x y, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun y _ => hx y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hI c c', hJ c c',
      mul_comm (finiteComplexInner (target c) (target c') ^ r), Complex.conj_mul']
    push_cast
    ring
  exact_mod_cast hkey

end Moment

section Barrier

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  {C : Type*} [Fintype C] [Nonempty C]

/-- **The purity bound for the moment.**  Dropping the non-negative off-diagonal overlaps leaves
the squared mass of the law, which is at least the reciprocal support size. -/
theorem inv_card_le_hsNormSq_replicaMoment (r : ℕ) (w : C → ℝ) (target : C → α → ℂ)
    (hw : ∀ c, 0 ≤ w c) (hsum : ∑ c, w c = 1)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1) :
    1 / (Fintype.card C : ℝ) ≤ hsNormSq (replicaMoment r w target) := by
  rw [hsNormSq_replicaMoment]
  have hdiag : ∀ c : C, w c ^ (2 : ℕ) =
      w c * w c * ‖finiteComplexInner (target c) (target c) ^ r‖ ^ (2 : ℕ) := by
    intro c
    rw [hunit c, one_pow, norm_one, one_pow, mul_one]
    ring
  have hstep : (∑ c, w c ^ (2 : ℕ)) ≤ ∑ c, ∑ c', w c * w c' *
      ‖finiteComplexInner (target c) (target c') ^ r‖ ^ (2 : ℕ) := by
    refine Finset.sum_le_sum fun c _ => ?_
    rw [hdiag c]
    refine Finset.single_le_sum
      (f := fun c' => w c * w c' * ‖finiteComplexInner (target c) (target c') ^ r‖ ^ (2 : ℕ))
      (fun c' _ => mul_nonneg (mul_nonneg (hw c) (hw c')) (sq_nonneg _)) (Finset.mem_univ c)
  exact le_trans (inv_card_le_sum_sq w hsum) hstep

theorem choose_pos_of_nonempty (r : ℕ) :
    0 < ((Fintype.card α + r - 1).choose r : ℝ) := by
  have hcard : 0 < Fintype.card α := Fintype.card_pos
  have hle : r ≤ Fintype.card α + r - 1 := by omega
  have := Nat.choose_pos hle
  exact_mod_cast this

/-- **`(22)`, `(23)`.**  The moment of a law on `N` targets is at squared Hilbert--Schmidt distance
at least `1/N - 1/h` from the normalized symmetric projector. -/
theorem hsNormSq_replicaMoment_sub_omega_ge (r : ℕ) (w : C → ℝ) (target : C → α → ℂ)
    (hw : ∀ c, 0 ≤ w c) (hsum : ∑ c, w c = 1)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1) :
    (Fintype.card C : ℝ)⁻¹ - (((Fintype.card α + r - 1).choose r : ℕ) : ℝ)⁻¹
      ≤ hsNormSq (replicaMoment r w target -
          ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ)⁻¹ •
            symReplicaProjection (α := α) r) := by
  have hh : (0 : ℝ) < (((Fintype.card α + r - 1).choose r : ℕ) : ℝ) :=
    choose_pos_of_nonempty (α := α) r
  have hPtrace : (symReplicaProjection (α := α) r).trace
      = ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ) := by
    rw [symReplicaProjection_trace]
    push_cast
    ring
  rw [hsNormSq_sub_normalized_projection (replicaMoment r w target) (symReplicaProjection r)
    (replicaMoment_conjTranspose r w target) (symReplicaProjection_conjTranspose r)
    (symReplicaProjection_mul_self r) (symReplicaProjection_mul_replicaMoment r w target)
    (replicaMoment_trace r w target hunit hsum) hh hPtrace]
  have hpurity := inv_card_le_hsNormSq_replicaMoment r w target hw hsum hunit
  rw [one_div] at hpurity
  linarith

/-- **`(23)`.**  The square-root form of the barrier. -/
theorem sqrt_le_hsNormSq_replicaMoment_sub_omega (r : ℕ) (w : C → ℝ) (target : C → α → ℂ)
    (hw : ∀ c, 0 ≤ w c) (hsum : ∑ c, w c = 1)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1) :
    Real.sqrt ((Fintype.card C : ℝ)⁻¹ - (((Fintype.card α + r - 1).choose r : ℕ) : ℝ)⁻¹)
      ≤ Real.sqrt (hsNormSq (replicaMoment r w target -
          ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ)⁻¹ •
            symReplicaProjection (α := α) r)) :=
  Real.sqrt_le_sqrt (hsNormSq_replicaMoment_sub_omega_ge r w target hw hsum hunit)

/-- **`(26)`, sharp form.**  A nontrivial raw target bound forces `N < a^r h`. -/
theorem lt_smul_choose_of_capacity_bound (N D r : ℕ) {a : ℝ} (ha : 0 < a) (hD : 0 < D)
    (h : (N : ℝ) * (a ^ r)⁻¹ * ((r.factorial : ℝ) / (D : ℝ) ^ r) < 1) :
    (N : ℝ) < a ^ r * (((D + r - 1).choose r : ℕ) : ℝ) := by
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have harp : (0 : ℝ) < a ^ r := pow_pos ha r
  have hstep : (N : ℝ) < a ^ r * ((D : ℝ) ^ r / (r.factorial : ℝ)) := by
    rw [mul_assoc, ← lt_div_iff₀ (by positivity)] at h
    refine lt_of_lt_of_le h (le_of_eq ?_)
    field_simp
  have hnat : ((D ^ r : ℕ) : ℝ) ≤ ((r.factorial * (D + r - 1).choose r : ℕ) : ℝ) := by
    exact_mod_cast pow_le_factorial_mul_choose D r hD
  push_cast at hnat
  have hquot : (D : ℝ) ^ r / (r.factorial : ℝ) ≤ (((D + r - 1).choose r : ℕ) : ℝ) := by
    rw [div_le_iff₀ hfac]
    calc (D : ℝ) ^ r ≤ (r.factorial : ℝ) * (((D + r - 1).choose r : ℕ) : ℝ) := hnat
      _ = (((D + r - 1).choose r : ℕ) : ℝ) * (r.factorial : ℝ) := by ring
  exact lt_of_lt_of_le hstep (mul_le_mul_of_nonneg_left hquot harp.le)

/-- **`(27)`.**  In the capacity regime the barrier sharpens to `(1 - a^r)/N`. -/
theorem capacity_barrier_lt (r : ℕ) (w : C → ℝ) (target : C → α → ℂ)
    (hw : ∀ c, 0 ≤ w c) (hsum : ∑ c, w c = 1)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1)
    {a : ℝ}
    (hcap : (Fintype.card C : ℝ) < a ^ r * (((Fintype.card α + r - 1).choose r : ℕ) : ℝ)) :
    (1 - a ^ r) / (Fintype.card C : ℝ)
      < hsNormSq (replicaMoment r w target -
          ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ)⁻¹ •
            symReplicaProjection (α := α) r) := by
  have hh : (0 : ℝ) < (((Fintype.card α + r - 1).choose r : ℕ) : ℝ) :=
    choose_pos_of_nonempty (α := α) r
  have hN : (0 : ℝ) < (Fintype.card C : ℝ) := by
    have := Fintype.card_pos (α := C)
    exact_mod_cast this
  have hmain := hsNormSq_replicaMoment_sub_omega_ge r w target hw hsum hunit
  have hinv : (((Fintype.card α + r - 1).choose r : ℕ) : ℝ)⁻¹
      < a ^ r / (Fintype.card C : ℝ) := by
    rw [lt_div_iff₀ hN, inv_mul_eq_div, div_lt_iff₀ hh]
    exact hcap
  have hsplit : (1 - a ^ r) / (Fintype.card C : ℝ)
      = (Fintype.card C : ℝ)⁻¹ - a ^ r / (Fintype.card C : ℝ) := by
    rw [sub_div, one_div]
  rw [hsplit]
  linarith

end Barrier

end

end GaloisForLFunctions.HTGeometry
