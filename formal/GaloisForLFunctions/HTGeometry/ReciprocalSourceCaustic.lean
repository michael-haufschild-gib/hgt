import GaloisForLFunctions.HTGeometry.ReciprocalSourceChart
import GaloisForLFunctions.HTGeometry.HankelRationalSingularities
import GaloisForLFunctions.HTGeometry.HankelSquareCatalecticant
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonHankelSecant

/-!
# The higher caustics in the reciprocal source chart

The critical reciprocal-horizon Jacobian of the unit jet `Z = 1 + ∑_{q=1}^{M} z_q t^q` at depths
`(m, s + m - 1)` is (up to sign) the Toeplitz section of the coefficients `h_q` of `Z²`, whose
column reversal is the square Hankel window `(h_{s+i+j})_{i,j<m}`.  Its corank-`≥ k` locus is
therefore the preimage, under the squaring automorphism `(12)` of the jet coordinates, of the
Hankel determinantal variety of the window `h_s, …, h_{s+2m-2}`.

For `s ≥ 1` (`s = s' + 1`, `M = s' + 2m - 1`): the window is the last `2m - 1` jet coordinates and
`h_1, …, h_{s'}` are free, so the caustic is cut out by `sourceIdeal`, the image of the secant
ideal `I_r` (`r = m - k`) of the window, and its coordinate ring is the Hankel secant ring of the
window with `s'` free variables adjoined.

* `HTGeometry.unitJetAt` : the unit jet at a point.
* `HTGeometry.sourceCaustic` : the corank-`≥ k` locus of the horizon Jacobian.
* `HTGeometry.sourceIdeal`, `HTGeometry.zeroLocus_sourceIdeal`.
* `HTGeometry.sourceRingEquiv` : `K[z] / sourceIdeal ≃ₐ K[x] / secantIdealUpTo`.
-/

namespace HTGeometry

open MvPolynomial

variable {K : Type} [Field K]

/-- The unit jet `Z(z) ∈ K[t]` at a point `z` of the unit-jet chart. -/
noncomputable def unitJetAt {M : ℕ} (z : Fin M → K) : Polynomial K := (unitJet K M).map (eval z)

theorem coeff_sq_unitJetAt {M : ℕ} (z : Fin M → K) (q : ℕ) :
    (unitJetAt z * unitJetAt z).coeff q = eval z (jetSqCoeff K M q) := by
  rw [unitJetAt, ← Polynomial.map_mul, Polynomial.coeff_map, jetSqCoeff, pow_two]

/-- **The caustic of the critical reciprocal horizon** at depths `(m, s + m - 1)`: the unit jets
where the horizon Jacobian has corank at least `k`. -/
def sourceCaustic (s m k M : ℕ) : Set (Fin M → K) :=
  {z | k ≤ m - (GaloisForLFunctions.HTGeometry.criticalReciprocalJacobian (unitJetAt z)
    (s + m - 1) m).rank}

theorem matrix_rank_neg {m : ℕ} (A : Matrix (Fin m) (Fin m) K) : (-A).rank = A.rank := by
  have h : -A = A * (-1 : Matrix (Fin m) (Fin m) K) := by rw [Matrix.mul_neg, Matrix.mul_one]
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det]
  rw [Matrix.det_neg, Matrix.det_one, mul_one]
  exact isUnit_neg_one.pow _

/-- **The horizon caustic is a Hankel rank locus**: corank `≥ k` iff the square Hankel window
`(h_{s+i+j})` of `Z²` has rank `≤ m - k`. -/
theorem mem_sourceCaustic_iff {s m k M : ℕ} (hm : 0 < m) (hk : k ≤ m) (z : Fin M → K) :
    z ∈ sourceCaustic s m k M ↔
      (Matrix.of fun i j : Fin m => (unitJetAt z * unitJetAt z).coeff (s + i + j)).rank ≤ m - k := by
  have h1 : (GaloisForLFunctions.HTGeometry.criticalReciprocalJacobian (unitJetAt z)
      (s + m - 1) m).rank
      = (GaloisForLFunctions.HTGeometry.shiftedHorizonHankel
          (fun q => (unitJetAt z * unitJetAt z).coeff q) s m).rank := by
    rw [GaloisForLFunctions.HTGeometry.criticalReciprocalJacobian_eq_neg_rectangularSchurToeplitz,
      matrix_rank_neg,
      GaloisForLFunctions.HTGeometry.rectangularSchurToeplitz_rank_eq_shiftedHorizonHankel _ _ _ hm]
  have hle := Matrix.rank_le_width
    (GaloisForLFunctions.HTGeometry.shiftedHorizonHankel
      (fun q => (unitJetAt z * unitJetAt z).coeff q) s m)
  have h2 : (Matrix.of fun i j : Fin m => (unitJetAt z * unitJetAt z).coeff (s + i + j))
      = GaloisForLFunctions.HTGeometry.shiftedHorizonHankel
          (fun q => (unitJetAt z * unitJetAt z).coeff q) s m := rfl
  rw [sourceCaustic, Set.mem_setOf_eq, h1, h2]
  omega

/-! ## Depth `s ≥ 1`: the window is the last `2m - 1` jet coordinates -/

section Cylinder

variable (K) in
/-- The window `h_{s'+1+n}` (`n < 2m - 1`) among the jet coordinates `h_1, …, h_{s'+2m-1}`. -/
noncomputable def windowEmbed (s' m : ℕ) :
    MvPolynomial (Fin (2 * m - 1)) K →ₐ[K] MvPolynomial (Fin (s' + (2 * m - 1))) K :=
  rename (Fin.natAdd s')

variable (K) in
/-- **The caustic ideal in the source chart** (depth `s = s' + 1`, rank `≤ r`): the secant ideal of
the window, pulled back along the squaring automorphism `(12)`. -/
noncomputable def sourceIdeal [CharZero K] (s' m r : ℕ) : Ideal (MvPolynomial (Fin (s' + (2 * m - 1))) K) :=
  ((RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (windowEmbed K s' m)).map
    (jetSqEquiv K (s' + (2 * m - 1)))

theorem eval_jetSq_window [CharZero K] {s' m : ℕ} (z : Fin (s' + (2 * m - 1)) → K)
    (g : MvPolynomial (Fin (2 * m - 1)) K) :
    eval z (jetSqEquiv K (s' + (2 * m - 1)) (windowEmbed K s' m g))
      = eval (fun n : Fin (2 * m - 1) => (unitJetAt z * unitJetAt z).coeff (s' + 1 + n)) g := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [windowEmbed, rename_C, ← algebraMap_eq, AlgEquiv.commutes, algebraMap_eq, eval_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul, hp, map_mul, windowEmbed, rename_X, jetSqEquiv_X, eval_X,
      ← coeff_sq_unitJetAt, Fin.val_natAdd]
    congr 2
    omega

theorem forall_mem_map_iff {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S]
    [RingHomClass F R S] (φ : F) (I : Ideal R) (ψ : S →+* K) :
    (∀ g ∈ I.map φ, ψ g = 0) ↔ ∀ g ∈ I, ψ (φ g) = 0 := by
  constructor
  · exact fun h g hg => h _ (Ideal.mem_map_of_mem _ hg)
  · intro h g hg
    have hle : I.map φ ≤ RingHom.ker ψ :=
      Ideal.map_le_iff_le_comap.mpr fun x hx => (RingHom.mem_ker).mpr (h x hx)
    exact hle hg

/-- **The zero locus of the source ideal is the horizon caustic** (depth `s = s' + 1`,
`1 ≤ k ≤ m`, rank `r = m - k`). -/
theorem zeroLocus_sourceIdeal [CharZero K] {s' m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (z : Fin (s' + (2 * m - 1)) → K) :
    (∀ g ∈ sourceIdeal K s' m (m - k), eval z g = 0) ↔ z ∈ sourceCaustic (s' + 1) m k (s' + (2 * m - 1)) := by
  rw [mem_sourceCaustic_iff (by omega) hkm]
  set w := fun n : Fin (2 * m - 1) => (unitJetAt z * unitJetAt z).coeff (s' + 1 + n)
  have key : (∀ g ∈ sourceIdeal K s' m (m - k), eval z g = 0)
      ↔ ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) (m - k), eval w g = 0 := by
    constructor
    · intro h g hg
      rw [← eval_jetSq_window]
      exact h _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))
    · intro h g hg
      have h1 : (RHTower.finiteHankelSecantIdeal K (2 * m - 1) (m - k)).map (windowEmbed K s' m)
          ≤ (RingHom.ker (eval z)).comap (jetSqEquiv K (s' + (2 * m - 1))) :=
        Ideal.map_le_iff_le_comap.mpr fun x hx => by
          rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, eval_jetSq_window]
          exact h x hx
      exact (Ideal.map_le_iff_le_comap.mpr h1) hg
  have hsq := GaloisForLFunctions.HTGeometry.squareCatalecticant_iff (K := K) (m := m) (r := m - k)
    (by omega) w
  have hmat : (Matrix.of fun i j : Fin m => (unitJetAt z * unitJetAt z).coeff (s' + 1 + i + j))
      = Matrix.of fun i j : Fin m => w ⟨i + j, by have := i.isLt; have := j.isLt; omega⟩ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, w]
    congr 1
    omega
  rw [key, hmat, hsq.1, hsq.2]

/-- Adjoining free variables after the window: the extended secant ideal is `secantIdealUpTo`. -/
theorem map_castAdd_secantIdeal (N r f : ℕ) (hrN : r ≤ N) :
    (RHTower.finiteHankelSecantIdeal K N r).map (rename (Fin.castAdd f))
      = secantIdealUpTo K (N + f) r (N - r) := by
  rw [RHTower.finiteHankelSecantIdeal, Ideal.map_span, secantIdealUpTo]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨c, hb, hmono, rfl⟩, rfl⟩
    refine ⟨c, fun i => by have := hb i; omega, hmono, fun i => by have := hb i; omega, ?_⟩
    rw [RHTower.finiteHankelMaximalMinorOver, RHTower.finiteHankelMaximalMinorOver, AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i i' => ?_
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X]
    rfl
  · rintro ⟨c, hb, hmono, hc, rfl⟩
    refine ⟨_, ⟨c, fun i => by have := hc i; omega, hmono, rfl⟩, ?_⟩
    rw [RHTower.finiteHankelMaximalMinorOver, RHTower.finiteHankelMaximalMinorOver, AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i i' => ?_
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X]
    rfl

theorem map_flip_window (s' m r : ℕ) (hr : r ≤ 2 * m - 1) :
    ((RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (windowEmbed K s' m)).map
        (renameEquiv K (finAddFlip (m := s') (n := 2 * m - 1)))
      = secantIdealUpTo K (2 * m - 1 + s') r (2 * m - 1 - r) := by
  rw [← map_castAdd_secantIdeal _ _ _ hr, RHTower.finiteHankelSecantIdeal, Ideal.map_span,
    Ideal.map_span, Ideal.map_span, Set.image_image]
  congr 1
  refine Set.image_congr fun p _ => ?_
  rw [windowEmbed, renameEquiv_apply, rename_rename,
    show (⇑(finAddFlip (m := s') (n := 2 * m - 1)) ∘ Fin.natAdd s') = Fin.castAdd s' from
      funext fun n => finAddFlip_apply_natAdd n s']

variable (K) in
/-- **The coordinate ring of the source caustic** (`s = s' + 1`) is the Hankel secant ring of the
window with the `s'` lower jets adjoined as free variables. -/
noncomputable def sourceRingEquiv [CharZero K] (s' m r : ℕ) (hr : r ≤ 2 * m - 1) :
    (MvPolynomial (Fin (s' + (2 * m - 1))) K ⧸ sourceIdeal K s' m r)
      ≃ₐ[K] (MvPolynomial (Fin (2 * m - 1 + s')) K ⧸ secantIdealUpTo K (2 * m - 1 + s') r (2 * m - 1 - r)) :=
  (Ideal.quotientEquivAlg _ _ (jetSqEquiv K (s' + (2 * m - 1))).symm (by
    rw [sourceIdeal]
    exact (Ideal.map_of_equiv (jetSqEquiv K (s' + (2 * m - 1))).toRingEquiv).symm)).trans
  (Ideal.quotientEquivAlg _ _ (renameEquiv K (finAddFlip (m := s') (n := 2 * m - 1)))
    (map_flip_window s' m r hr).symm)

/-- **The source caustics (`s ≥ 1`) have rational singularities.** -/
theorem sourceCaustic_hasRationalSingularities [CharZero K] {s' m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    HasRationalSingularities K (MvPolynomial (Fin (s' + (2 * m - 1))) K ⧸ sourceIdeal K s' m (m - k)) :=
  (secantRingUpTo_hasRationalSingularities K (N := 2 * m - 1 + s') (r := m - k)
    (j := 2 * m - 1 - (m - k)) (by omega) (by omega)).of_algEquiv
    (sourceRingEquiv K s' m (m - k) (by omega)).symm

end Cylinder

end HTGeometry
