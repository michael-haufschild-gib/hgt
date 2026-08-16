import GaloisForLFunctions.HTGeometry.QuadOneNoAffineConnection

/-!
# A rational affine connection of `z ↦ z² + 1` cannot exist

Away from the critical point `0` the affine-connection equation `4z²·a(z²+1) = 2z·a(z) − 2`
transports poles in both directions.  Forward, because the term `2z·a(z)` dominates the constant
`−2` exactly when `a` has a pole; backward, because a pole of `a` at `z² + 1` cannot be matched by a
right-hand side whose two terms are both regular.

Both directions are fatal.  The critical value `1` has the infinite forward orbit `1, 2, 5, 26, …`,
so a pole there produces infinitely many poles.  The preimage `i` of the critical point is neither
periodic nor postcritical, so it carries an injective backward orbit avoiding `0`, and a pole at the
critical point produces infinitely many poles along it.  Since one of the two points must carry a
pole, and a nonzero rational function has finitely many zeros and poles, no solution exists.

Consequently `z ↦ z² + 1` admits no invariant affine structure, which is the obstruction that closes
the fixed branch of the orbifold-tail trichotomy at jet order two.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## Local data away from the critical point -/

/-- Away from the critical point the map is locally injective: `z² + 1` takes its value at `c` to
order one. -/
theorem rootMultiplicity_quadOne_sub_eval {c : ℂ} (hc : c ≠ 0) :
    rootMultiplicity c (quadOne - Polynomial.C (quadOne.eval c)) = 1 := by
  have hpoly : quadOne - Polynomial.C (quadOne.eval c)
      = Polynomial.X ^ 2 - Polynomial.C (c ^ 2) := by
    rw [quadOne_eval, quadOne,
      show Polynomial.C (c ^ 2 + 1) = Polynomial.C (c ^ 2) + Polynomial.C 1 from by rw [map_add]]
    ring
  have hne : (Polynomial.X ^ 2 - Polynomial.C (c ^ 2) : Polynomial ℂ) ≠ 0 :=
    (monic_X_pow_sub_C (c ^ 2) (by norm_num)).ne_zero
  have hroot : (Polynomial.X ^ 2 - Polynomial.C (c ^ 2) : Polynomial ℂ).eval c = 0 := by
    simp
  have hderiv : (derivative (Polynomial.X ^ 2 - Polynomial.C (c ^ 2) : Polynomial ℂ)).eval c ≠ 0 := by
    have hd : (derivative (Polynomial.X ^ 2 - Polynomial.C (c ^ 2) : Polynomial ℂ))
        = Polynomial.C 2 * Polynomial.X := by
      rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_one]
      norm_num
    rw [hd]
    simp only [eval_mul, eval_C, eval_X]
    exact mul_ne_zero (by norm_num) hc
  rw [hpoly]
  exact rootMultiplicity_eq_one hne hroot hderiv

theorem ratOrder_quadOneLead_of_ne_zero {c : ℂ} (hc : c ≠ 0) :
    ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2)) c = 0 := by
  have hroot : ¬ (Polynomial.C 4 * Polynomial.X ^ 2 : Polynomial ℂ).IsRoot c := by
    simp only [IsRoot, eval_mul, eval_C, eval_pow, eval_X]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)
  rw [ratOrder_algebraMap, rootMultiplicity_eq_zero hroot, Nat.cast_zero]

theorem ratOrder_quadOneSlope_of_ne_zero {c : ℂ} (hc : c ≠ 0) :
    ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X)) c = 0 := by
  have hroot : ¬ (Polynomial.C 2 * Polynomial.X : Polynomial ℂ).IsRoot c := by
    simp only [IsRoot, eval_mul, eval_C, eval_X]
    exact mul_ne_zero (by norm_num) hc
  rw [ratOrder_algebraMap, rootMultiplicity_eq_zero hroot, Nat.cast_zero]

theorem ratOrder_quadOneCurv (c : ℂ) :
    ratOrder (-algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2)) c = 0 := by
  have hroot : ¬ (Polynomial.C 2 : Polynomial ℂ).IsRoot c := by simp
  rw [ratOrder_neg (algebraMap_ne_zero_of_ne_zero quadOneCurv_ne_zero), ratOrder_algebraMap,
    rootMultiplicity_eq_zero hroot, Nat.cast_zero]

/-- Away from the critical point the two sides of the affine-connection equation compare the order
of `a` at `c` with its order at `z² + 1`. -/
theorem ratOrder_quadOne_affine_side {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsQuadOneAffineConnection a) {c : ℂ} (hc : c ≠ 0) :
    ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
        + -algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2)) c
      = ratOrder a (quadOne.eval c) := by
  have heq' := isQuadOneAffineConnection_def heq
  have hdeg : quadOne.natDegree ≠ 0 := by rw [natDegree_quadOne]; norm_num
  have hA4 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneLead_ne_zero
  have hsub0 := quadOneSubst_ne_zero ha
  have hswap : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
      + -algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2)
        * ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_not_isConst a := by
    rw [heq']; ring
  rw [hswap, ratOrder_mul hA4 hsub0, ratOrder_quadOneLead_of_ne_zero hc, zero_add,
    ratOrder_ratFuncSubstitution hdeg quadOne_not_isConst ha c, rootMultiplicity_quadOne_sub_eval hc,
    Nat.cast_one, mul_one]

theorem quadOne_affine_side_ne_zero {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsQuadOneAffineConnection a) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
      + -algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 := by
  have heq' := isQuadOneAffineConnection_def heq
  have hswap : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
      + -algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 4 * Polynomial.X ^ 2)
        * ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_not_isConst a := by
    rw [heq']; ring
  rw [hswap]
  exact mul_ne_zero (algebraMap_ne_zero_of_ne_zero quadOneLead_ne_zero) (quadOneSubst_ne_zero ha)

/-! ## Transport of poles -/

/-- **Poles move forward.**  A pole away from the critical point produces a pole at its image. -/
theorem quadOne_affine_pole_forward {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsQuadOneAffineConnection a) {c : ℂ} (hc : c ≠ 0) (hpole : ratOrder a c < 0) :
    ratOrder a (quadOne.eval c) < 0 := by
  have hA2X : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneSlope_ne_zero
  have hA2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneCurv_ne_zero
  set u : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
    with hu
  set v : RatFunc ℂ := -algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) with hv
  have hu0 : u ≠ 0 := mul_ne_zero hA2X ha
  have hv0 : v ≠ 0 := by rw [hv]; exact neg_ne_zero.mpr hA2
  have hordu : ratOrder u c = ratOrder a c := by
    rw [hu, ratOrder_mul hA2X ha, ratOrder_quadOneSlope_of_ne_zero hc, zero_add]
  have hordv : ratOrder v c = 0 := by rw [hv]; exact ratOrder_quadOneCurv c
  have hside := ratOrder_quadOne_affine_side ha heq hc
  rw [← hu, ← hv] at hside
  have hsumne : u + v ≠ 0 := by
    have h := quadOne_affine_side_ne_zero ha heq
    rwa [← hu, ← hv] at h
  -- `u = (u + v) + (-v)`, so the sum inherits the pole
  have husum : u = (u + v) + (-v) := by ring
  have hmin := min_le_ratOrder_add hsumne (neg_ne_zero.mpr hv0) (by rw [← husum]; exact hu0) c
  rw [← husum, hordu, ratOrder_neg hv0, hordv, hside] at hmin
  omega

/-- **Poles move backward.**  Every preimage away from the critical point of a pole is a pole. -/
theorem quadOne_affine_pole_backward {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsQuadOneAffineConnection a) {c : ℂ} (hc : c ≠ 0)
    (hpole : ratOrder a (quadOne.eval c) < 0) : ratOrder a c < 0 := by
  by_contra hreg
  rw [not_lt] at hreg
  have hA2X : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneSlope_ne_zero
  have hA2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero quadOneCurv_ne_zero
  set u : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2 * Polynomial.X) * a
    with hu
  set v : RatFunc ℂ := -algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) with hv
  have hu0 : u ≠ 0 := mul_ne_zero hA2X ha
  have hv0 : v ≠ 0 := by rw [hv]; exact neg_ne_zero.mpr hA2
  have hordu : ratOrder u c = ratOrder a c := by
    rw [hu, ratOrder_mul hA2X ha, ratOrder_quadOneSlope_of_ne_zero hc, zero_add]
  have hordv : ratOrder v c = 0 := by rw [hv]; exact ratOrder_quadOneCurv c
  have hside := ratOrder_quadOne_affine_side ha heq hc
  rw [← hu, ← hv] at hside
  have hsumne : u + v ≠ 0 := by
    have h := quadOne_affine_side_ne_zero ha heq
    rwa [← hu, ← hv] at h
  have hmin := min_le_ratOrder_add hu0 hv0 hsumne c
  rw [hordu, hordv, hside] at hmin
  omega

/-! ## The two infinite orbits -/

theorem quadOneOrbit_lt_succ (n : ℕ) : quadOneOrbit n < quadOneOrbit (n + 1) := by
  have h : quadOneOrbit n ≤ quadOneOrbit n ^ 2 :=
    Nat.le_self_pow (by norm_num) (quadOneOrbit n)
  rw [quadOneOrbit]
  omega

theorem strictMono_quadOneOrbit : StrictMono quadOneOrbit :=
  strictMono_nat_of_lt_succ quadOneOrbit_lt_succ

theorem quadOneOrbit_succ_ne_zero (n : ℕ) : quadOneOrbit (n + 1) ≠ 0 := by
  rw [quadOneOrbit]
  omega

theorem quadOne_eval_quadOneOrbit (n : ℕ) :
    quadOne.eval ((quadOneOrbit n : ℕ) : ℂ) = ((quadOneOrbit (n + 1) : ℕ) : ℂ) := by
  rw [quadOne_eval, quadOneOrbit]
  push_cast
  ring

/-- The critical value carries no pole. -/
theorem quadOne_affine_no_pole_at_one {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsQuadOneAffineConnection a) : 0 ≤ ratOrder a 1 := by
  by_contra hpole
  rw [not_le] at hpole
  -- every point of the forward orbit `1, 2, 5, 26, …` is a pole
  have horbit : ∀ n : ℕ, ratOrder a ((quadOneOrbit (n + 1) : ℕ) : ℂ) < 0 := by
    intro n
    induction n with
    | zero =>
        have h1 : ((quadOneOrbit 1 : ℕ) : ℂ) = 1 := by norm_num [quadOneOrbit]
        rw [h1]
        exact hpole
    | succ n ih =>
        have hne : ((quadOneOrbit (n + 1) : ℕ) : ℂ) ≠ 0 := by
          simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (quadOneOrbit_succ_ne_zero n)
        have := quadOne_affine_pole_forward ha heq hne ih
        rwa [quadOne_eval_quadOneOrbit] at this
  -- the orbit is injective, so the poles are infinite
  have hinj : Function.Injective (fun n : ℕ => ((quadOneOrbit (n + 1) : ℕ) : ℂ)) := by
    intro m n hmn
    simp only at hmn
    have := Nat.cast_injective (R := ℂ) hmn
    have := strictMono_quadOneOrbit.injective this
    omega
  have hsub : Set.range (fun n : ℕ => ((quadOneOrbit (n + 1) : ℕ) : ℂ))
      ⊆ {c : ℂ | ratOrder a c ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    exact ne_of_lt (horbit n)
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder ha).subset hsub)

/-- The critical point carries no pole. -/
theorem quadOne_affine_no_pole_at_zero {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsQuadOneAffineConnection a) : 0 ≤ ratOrder a 0 := by
  by_contra hpole
  rw [not_le] at hpole
  have hdeg : quadOne.natDegree ≠ 0 := by rw [natDegree_quadOne]; norm_num
  -- `i` is a preimage of the critical point, hence a pole
  have hI : quadOne.eval Complex.I = 0 := by rw [quadOne_eval, Complex.I_sq]; ring
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hIpole : ratOrder a Complex.I < 0 :=
    quadOne_affine_pole_backward ha heq hIne (by rw [hI]; exact hpole)
  -- `i` is neither periodic nor postcritical, so it carries an injective backward orbit
  obtain ⟨b, hb0, hstep, hinj, hcrit⟩ :=
    exists_backward_orbit hdeg aperiodic_quadOne_I postcritical_quadOne_ne_I
  have horbit : ∀ n : ℕ, ratOrder a (b n) < 0 := by
    intro n
    induction n with
    | zero => rw [hb0]; exact hIpole
    | succ n ih =>
        have hne : b (n + 1) ≠ 0 := by
          intro h
          exact hcrit n (by rw [h, derivative_quadOne]; simp)
        exact quadOne_affine_pole_backward ha heq hne (by rw [hstep n]; exact ih)
  have hsub : Set.range b ⊆ {c : ℂ | ratOrder a c ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    exact ne_of_lt (horbit n)
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder ha).subset hsub)

/-- The zero function is not an affine connection: the curvature term `−2` survives. -/
theorem not_isQuadOneAffineConnection_zero : ¬ IsQuadOneAffineConnection 0 := by
  intro heq
  have heq' := isQuadOneAffineConnection_def heq
  rw [map_zero, mul_zero, mul_zero, zero_sub, eq_comm, neg_eq_zero] at heq'
  exact algebraMap_ne_zero_of_ne_zero quadOneCurv_ne_zero heq'

/-- **`z ↦ z² + 1` carries no rational affine connection.** -/
theorem quadOne_no_affine_connection (a : RatFunc ℂ) : ¬ IsQuadOneAffineConnection a := by
  intro heq
  rcases eq_or_ne a 0 with rfl | ha
  · exact not_isQuadOneAffineConnection_zero heq
  · exact quadOne_no_affine_connection_regular ha (quadOne_affine_no_pole_at_zero ha heq)
      (quadOne_affine_no_pole_at_one ha heq) heq

end GaloisForLFunctions.HTGeometry
