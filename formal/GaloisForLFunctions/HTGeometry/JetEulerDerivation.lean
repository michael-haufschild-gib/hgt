import GaloisForLFunctions.HTGeometry.JetStripStep

/-!
# The Euler derivation of the weight grading

The derivation `Eu` of the free jet field determined by `Eu(y_j) = j·y_j` is the infinitesimal
generator of the weighted torus.  It kills every weight-zero coordinate `z_j = y_j/y₁^j` and
commutes with the jet derivation up to `δ`:

`⁅Eu, δ⁆ = δ`.

Consequently `Eu` annihilates the whole tower of weight-zero shifts `s_M`, and the chain rule turns
that into the Euler relation

`y₁·∂_1 v = −∑_{j ≥ 2} j·z_j·(y₁^j·∂_j v)`

for every such `v`: the partial in the first coordinate is determined by the higher descents.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- The Euler derivation of the polynomial ring: `y_j ↦ j·y_j`. -/
def jetEulerPoly : Derivation C (JetPoly C Unit) (JetField C Unit) :=
  (Algebra.linearMap (JetPoly C Unit) (JetField C Unit)).compDer
    (MvPolynomial.mkDerivation C fun p : Unit × ℕ =>
      ((p.2 : ℕ) : JetPoly C Unit) * MvPolynomial.X p)

/-- **The Euler derivation of the weight grading.** -/
def jetEuler : Derivation C (JetField C Unit) (JetField C Unit) :=
  fractionRingDerivation jetEulerPoly

omit [CharZero C] in
@[simp] theorem jetEuler_jet (p : Unit × ℕ) :
    jetEuler (JetField.jet p : JetField C Unit)
      = ((p.2 : ℕ) : JetField C Unit) * JetField.jet p := by
  rw [jetEuler, JetField.jet, fractionRingDerivation_algebraMap]
  show (Algebra.linearMap (JetPoly C Unit) (JetField C Unit))
      ((MvPolynomial.mkDerivation C fun q : Unit × ℕ =>
        ((q.2 : ℕ) : JetPoly C Unit) * MvPolynomial.X q) (MvPolynomial.X p)) = _
  rw [MvPolynomial.mkDerivation_X]
  show algebraMap (JetPoly C Unit) (JetField C Unit)
      (((p.2 : ℕ) : JetPoly C Unit) * MvPolynomial.X p) = _
  rw [map_mul, map_natCast]

theorem jetEuler_jetRatio (j : ℕ) : jetEuler (jetRatio j : JetField C Unit) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hmul : (jetRatio j : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit) ^ j
      = (JetField.jet ((), j) : JetField C Unit) := by
    rw [jetRatio]
    field_simp
  have hpow : jetEuler ((JetField.jet ((), 1) : JetField C Unit) ^ j)
      = (j : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit) ^ j := by
    have h := (jetEuler (C := C)).leibniz_pow (JetField.jet ((), 1) : JetField C Unit) j
    simp only [smul_eq_mul, jetEuler_jet] at h
    rw [h]
    rcases j with _ | i
    · simp
    · have hs : (JetField.jet ((), 1) : JetField C Unit) ^ (i + 1)
          = (JetField.jet ((), 1) : JetField C Unit) ^ i
            * (JetField.jet ((), 1) : JetField C Unit) := by rw [pow_succ]
      simp only [Nat.add_sub_cancel]
      rw [hs]
      push_cast
      ring
  have hleib := (jetEuler (C := C)).leibniz (jetRatio j : JetField C Unit)
    ((JetField.jet ((), 1) : JetField C Unit) ^ j)
  simp only [smul_eq_mul] at hleib
  rw [hmul, jetEuler_jet, hpow] at hleib
  have hcancel : jetEuler (jetRatio j : JetField C Unit)
      * (JetField.jet ((), 1) : JetField C Unit) ^ j = 0 := by
    have hz : (jetRatio j : JetField C Unit) * ((j : JetField C Unit)
        * (JetField.jet ((), 1) : JetField C Unit) ^ j)
        = (j : JetField C Unit) * (JetField.jet ((), j) : JetField C Unit) := by
      rw [← hmul]
      ring
    rw [hz] at hleib
    linear_combination -hleib
  exact (mul_eq_zero.mp hcancel).resolve_right (pow_ne_zero j hy1)

omit [CharZero C] in
/-- **The Euler derivation commutes with the jet derivation up to `δ`.** -/
theorem commutator_jetEuler_jetDerivation :
    ⁅jetEuler (C := C), JetField.jetDerivation (C := C) (ι := Unit)⁆
      = JetField.jetDerivation (C := C) (ι := Unit) := by
  refine JetField.derivation_ext fun q => ?_
  rw [Derivation.commutator_apply, JetField.jetDerivation_jet, jetEuler_jet, jetEuler_jet]
  have hleib := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz
    (((q.2 : ℕ) : JetField C Unit)) (JetField.jet q : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  have hcast : JetField.jetDerivation (((q.2 : ℕ) : JetField C Unit)) = 0 := by
    rw [show (((q.2 : ℕ) : JetField C Unit))
        = algebraMap C (JetField C Unit) (((q.2 : ℕ) : C)) from
      (map_natCast (algebraMap C (JetField C Unit)) q.2).symm, Derivation.map_algebraMap]
  rw [hleib, hcast, JetField.jetDerivation_jet, mul_zero, add_zero]
  push_cast
  ring

omit [CharZero C] in
/-- The commutation rule `Eu(δ u) = δ(Eu u) + δ u`. -/
theorem jetEuler_jetDerivation (u : JetField C Unit) :
    jetEuler (JetField.jetDerivation u)
      = JetField.jetDerivation (jetEuler u) + JetField.jetDerivation u := by
  have h := congrArg (fun D : Derivation C (JetField C Unit) (JetField C Unit) => D u)
    (commutator_jetEuler_jetDerivation (C := C))
  simp only [Derivation.commutator_apply] at h
  linear_combination h

/-- The Euler derivation commutes with the weight-zero derivation. -/
theorem jetEuler_jetNabla (u : JetField C Unit) :
    jetEuler (jetNabla u) = jetNabla (jetEuler u) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hinv : jetEuler ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      = -((JetField.jet ((), 1) : JetField C Unit))⁻¹ := by
    have h := (jetEuler (C := C)).leibniz_inv (JetField.jet ((), 1) : JetField C Unit)
    rw [jetEuler_jet] at h
    simp only [smul_eq_mul, Nat.cast_one, one_mul] at h
    rw [h]
    field_simp
  rw [jetNabla_apply, jetNabla_apply, div_eq_mul_inv, div_eq_mul_inv]
  have h := (jetEuler (C := C)).leibniz (JetField.jetDerivation u)
    ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
  simp only [smul_eq_mul] at h
  rw [h, hinv, jetEuler_jetDerivation]
  ring

/-! ## The Euler derivation annihilates the shift tower -/

theorem jetEuler_of_order_zero {v : JetField C Unit}
    (hv : ∀ k : ℕ, k ≠ 0 → JetField.pd ((), k) v = 0) : jetEuler v = 0 := by
  classical
  have hmem := (mem_freeCoordinateField_iff (C := C) (σ := Unit × ℕ)
      (↑({((), 0)} : Finset (Unit × ℕ)) : Set (Unit × ℕ)) v).mpr (by
    rintro ⟨⟨⟩, k⟩ hk
    exact hv k (by rintro rfl; exact hk (by simp)))
  have h := freeCoordinate_chainRule ({((), 0)} : Finset (Unit × ℕ))
    (jetEuler (C := C)) hmem
  rw [Finset.sum_singleton] at h
  refine h.trans (mul_eq_zero_of_left ?_ _)
  exact (show jetEuler (JetField.jet ((), 0) : JetField C Unit) = 0 from by
    rw [jetEuler_jet]; simp)

omit [CharZero C] in
theorem jetEuler_mul_eq_zero {a b : JetField C Unit} (ha : jetEuler a = 0)
    (hb : jetEuler b = 0) : jetEuler (a * b) = 0 := by
  have hleib := (jetEuler (C := C)).leibniz a b
  simp only [smul_eq_mul] at hleib
  rw [hleib, ha, hb, mul_zero, mul_zero, add_zero]

omit [CharZero C] in
theorem jetEuler_natCast (n : ℕ) : jetEuler ((n : ℕ) : JetField C Unit) = 0 := by
  rw [show ((n : ℕ) : JetField C Unit) = algebraMap C (JetField C Unit) ((n : ℕ) : C) from
    (map_natCast (algebraMap C (JetField C Unit)) n).symm, Derivation.map_algebraMap]

/-- **The Euler derivation annihilates the shift tower.** -/
theorem jetEuler_substitutionShiftRatio (R : RatFunc C) {k : ℕ} (hk : 1 ≤ k) :
    jetEuler (substitutionShiftRatio R k) = 0 := by
  have hρ1 : jetEuler (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
    refine jetEuler_of_order_zero fun m hm => ?_
    rw [pd_comm, pd_substitutionDeriv_eq_zero R hm, map_zero]
  induction k, hk using Nat.le_induction with
  | base => rw [substitutionShiftRatio_one, map_zero]
  | succ k hk ih =>
      rw [substitutionShiftRatio_succ, map_add, map_add, jetEuler_jetNabla, ih, map_zero,
        jetEuler_mul_eq_zero (jetEuler_mul_eq_zero (jetEuler_natCast k) (jetEuler_jetRatio 2)) ih,
        jetEuler_mul_eq_zero hρ1 (jetEuler_jetRatio k)]
      simp

/-! ## The Euler relation -/

/-- **The Euler derivation as a finite sum of partials.** -/
theorem jetEuler_sum (K : ℕ) {v : JetField C Unit}
    (hv : ∀ j : ℕ, K < j → JetField.pd ((), j) v = 0) :
    jetEuler v = ∑ j ∈ Finset.range (K + 1),
      (j : JetField C Unit) * (JetField.jet ((), j) : JetField C Unit)
        * JetField.pd ((), j) v := by
  classical
  set S : Finset (Unit × ℕ) := (Finset.range (K + 1)).image (fun j => ((), j)) with hSdef
  have hinj : Set.InjOn (fun j : ℕ => ((), j)) (Finset.range (K + 1)) := by
    intro a _ b _ hab
    exact congrArg Prod.snd hab
  have hmem := (mem_freeCoordinateField_iff (C := C) (σ := Unit × ℕ)
      (↑S : Set (Unit × ℕ)) v).mpr (by
    rintro ⟨⟨⟩, k⟩ hk
    refine hv k ?_
    by_contra hcon
    exact hk (by
      simp only [hSdef, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
      exact ⟨k, by omega, rfl⟩))
  have h := freeCoordinate_chainRule S (jetEuler (C := C)) hmem
  refine h.trans ?_
  rw [hSdef, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact jetEuler_jet ((), j)

end

end GaloisForLFunctions.HTGeometry
