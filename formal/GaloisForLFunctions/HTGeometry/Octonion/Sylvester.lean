import GaloisForLFunctions.HTGeometry.Octonion.Conjugacy

open scoped Quaternion

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The real-linear Sylvester operator `R_s - L_q`. -/
def sylvesterDifferenceLinear (s q : RealOctonion) :
    RealOctonion →ₗ[ℝ] RealOctonion where
  toFun x := resolventDifference s q x
  map_add' x y := by
    unfold resolventDifference leftAction rightAction
    rw [add_mul, mul_add, sub_add_sub_comm]
  map_smul' r x := by
    unfold resolventDifference leftAction rightAction
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    rfl

set_option maxHeartbeats 800000 in
/-- A kernel vector of `R_s - L_q` forces `Q_s(q)` to vanish.  The proof brings the
three relevant octonions into their Artin two-generated associative subalgebra, rather than
assuming global associativity. -/
theorem resolventDifference_eq_zero_of_not_mem_conjugacySphere
    (s q x : RealOctonion) (hsphere : s ∉ conjugacySphere q)
    (hzero : resolventDifference s q x = 0) : x = 0 := by
  by_contra hx
  have hxs : x * s = q * x := sub_eq_zero.mp (by
    simpa [resolventDifference, leftAction, rightAction] using hzero)
  let M := generatedSubmodule q x
  have hq : q ∈ M := s_mem_generatedSubmodule q x
  have hxM : x ∈ M := q_mem_generatedSubmodule q x
  have hinv : inverse x ∈ M := inverse_mem_generatedSubmodule q x x hxM
  have hqx : q * x ∈ M := mul_mem_generatedSubmodule q x q x hq hxM
  have hseq : s = inverse x * (q * x) := by
    calc
      s = 1 * s := (one_mul s).symm
      _ = (inverse x * x) * s := by rw [inverse_mul x hx]
      _ = inverse x * (x * s) := inverse_mul_associates x s
      _ = inverse x * (q * x) := by rw [hxs]
  have hs : s ∈ M := by
    rw [hseq]
    exact mul_mem_generatedSubmodule q x _ _ hinv hqx
  have hsbar : star s ∈ M := star_mem_generatedSubmodule q x s hs
  have hquad : quadratic s q ∈ M := by
    unfold quadratic
    apply Submodule.add_mem
    · apply Submodule.sub_mem
      · exact mul_mem_generatedSubmodule q x q q hq hq
      · exact mul_mem_generatedSubmodule q x _ q
          (scalarEmbed_mem_generatedSubmodule q x _) hq
    · exact scalarEmbed_mem_generatedSubmodule q x _
  have hxssbar : (x * s) * star s = x * (s * star s) :=
    sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule q x x s (star s)
      hxM hs hsbar)
  have hqxs : (q * x) * s = q * (x * s) :=
    sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule q x q x s hq hxM hs)
  have hqxsbar : (q * x) * star s = q * (x * star s) :=
    sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule q x q x (star s)
      hq hxM hsbar)
  have hnorm : x * (s * star s) = scalarEmbed (normSq s) * x := by
    rw [mul_star_self_eq_scalarEmbed, mul_scalarEmbed, scalarEmbed_mul]
  have htrace : q * (x * (star s + s)) =
      (scalarEmbed (2 * s.1.re) * q) * x := by
    rw [add_comm (star s) s, add_star_eq_scalarEmbed]
    calc
      q * (x * scalarEmbed (2 * s.1.re)) = q * ((2 * s.1.re) • x) := by
        rw [mul_scalarEmbed]
      _ = scalarEmbed (2 * s.1.re) * (q * x) := by
        rw [mul_smul_comm, scalarEmbed_mul]
      _ = (scalarEmbed (2 * s.1.re) * q) * x :=
        (scalarEmbed_associates _ _ _).symm
  have hcombine : q * (x * star s) + q * (x * s) = q * (x * (star s + s)) := by
    calc
      q * (x * star s) + q * (x * s) = q * (x * star s + x * s) := by
        rw [mul_add]
      _ = q * (x * (star s + s)) := by
        conv_rhs => rw [mul_add]
  have hfactor : resolventDifference (star s) q (resolventDifference s q x) =
      quadratic s q * x := by
    unfold resolventDifference
    simp only [leftAction, rightAction, quadratic, sub_mul, mul_sub]
    calc
      (x * s) * star s - (q * x) * star s - (q * (x * s) - q * (q * x)) =
          x * (s * star s) - q * (x * star s) - q * (x * s) + q * (q * x) := by
            rw [hxssbar, hqxsbar]
            abel
      _ = scalarEmbed (normSq s) * x - q * (x * (star s + s)) + (q * q) * x := by
            rw [hnorm, IsAlternative.mul_alternative_left]
            rw [← hcombine]
            abel
      _ = (q * q - scalarEmbed (2 * s.1.re) * q + scalarEmbed (normSq s)) * x := by
            rw [htrace, add_mul, sub_mul]
            abel
  have hqzero : quadratic s q * x = 0 := by
    rw [← hfactor, hzero]
    simp [resolventDifference, leftAction, rightAction]
  have hright : (quadratic s q * x) * inverse x =
      quadratic s q * (x * inverse x) :=
    sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule q x
      (quadratic s q) x (inverse x) hquad hxM hinv)
  have hquadratic : quadratic s q = 0 := by
    calc
      quadratic s q = quadratic s q * 1 := (mul_one _).symm
      _ = quadratic s q * (x * inverse x) := by rw [mul_inverse x hx]
      _ = (quadratic s q * x) * inverse x := hright.symm
      _ = 0 := by rw [hqzero, zero_mul]
  exact hsphere ((mem_conjugacySphere_iff_quadratic_eq_zero s q).mpr hquadratic)

/-- Off the conjugacy sphere, `R_s - L_q` has trivial kernel. -/
theorem sylvesterDifferenceLinear_injective_of_not_mem_conjugacySphere
    (s q : RealOctonion) (hsphere : s ∉ conjugacySphere q) :
    Function.Injective (sylvesterDifferenceLinear s q) := by
  intro x y hxy
  have hzero : resolventDifference s q (x - y) = 0 := by
    calc
      resolventDifference s q (x - y) =
          resolventDifference s q x - resolventDifference s q y := by
            unfold resolventDifference leftAction rightAction
            rw [sub_mul, mul_sub, sub_sub_sub_comm]
      _ = 0 := sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp
    (resolventDifference_eq_zero_of_not_mem_conjugacySphere s q (x - y)
      hsphere hzero)

/-- Lemma 8.5's off-sphere invertibility conclusion, as an explicit real-linear equivalence. -/
noncomputable def sylvesterDifferenceEquivOfNotMemConjugacySphere
    (s q : RealOctonion) (hsphere : s ∉ conjugacySphere q) :
    RealOctonion ≃ₗ[ℝ] RealOctonion :=
  LinearEquiv.ofBijective (sylvesterDifferenceLinear s q)
    ⟨sylvesterDifferenceLinear_injective_of_not_mem_conjugacySphere s q hsphere,
      LinearMap.surjective_of_injective
        (sylvesterDifferenceLinear_injective_of_not_mem_conjugacySphere s q hsphere)⟩

/-- Two fixed quaternionic coordinate units inside the real octonions. -/
def standardQuaternionUnitI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def standardQuaternionUnitJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
def standardOctonionUnitI : RealOctonion := mk standardQuaternionUnitI 0
def standardOctonionUnitJ : RealOctonion := mk standardQuaternionUnitJ 0

private theorem quaternion_eq_zero_of_re_eq_zero_of_commutators (a : ℍ[ℝ])
    (hre : a.re = 0)
    (hi : a * standardQuaternionUnitI - standardQuaternionUnitI * a = 0)
    (hj : a * standardQuaternionUnitJ - standardQuaternionUnitJ * a = 0) : a = 0 := by
  rcases a with ⟨a0, a1, a2, a3⟩
  change a0 = 0 at hre
  have hiJ := congrArg (fun z : ℍ[ℝ] => z.imJ) hi
  have hiK := congrArg (fun z : ℍ[ℝ] => z.imK) hi
  have hjK := congrArg (fun z : ℍ[ℝ] => z.imK) hj
  norm_num [standardQuaternionUnitI, standardQuaternionUnitJ,
    QuaternionAlgebra.mk_mul_mk] at hiJ hiK hjK
  have ha2 : a2 = 0 := by linarith [hiK]
  apply Quaternion.ext <;> simp [hre, hjK, ha2, hiJ]

private theorem snd_eq_zero_of_commutator_standardOctonionUnitI (u : RealOctonion)
    (h : u * standardOctonionUnitI - standardOctonionUnitI * u = 0) : u.2 = 0 := by
  have h2 := congrArg Prod.snd h
  change (u * standardOctonionUnitI).2 - (standardOctonionUnitI * u).2 = 0 at h2
  rw [mul_snd, mul_snd] at h2
  have h2' : standardOctonionUnitI.2 * u.1 + u.2 * star standardOctonionUnitI.1 -
      (u.2 * standardOctonionUnitI.1 + standardOctonionUnitI.2 * star u.1) = 0 := h2
  have hIzero : standardOctonionUnitI.2 = 0 := rfl
  have h2'' : u.2 * star standardOctonionUnitI.1 - u.2 * standardOctonionUnitI.1 = 0 := by
    simpa only [hIzero, zero_mul, zero_add, add_zero] using h2'
  have hstarI : star standardOctonionUnitI.1 = -standardOctonionUnitI.1 := by
    change star (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = -(⟨0, 1, 0, 0⟩ : ℍ[ℝ])
    rw [QuaternionAlgebra.star_mk]
    norm_num
  rw [hstarI, mul_neg] at h2''
  have htwice : u.2 * standardOctonionUnitI.1 + u.2 * standardOctonionUnitI.1 = 0 := by
    calc
      u.2 * standardOctonionUnitI.1 + u.2 * standardOctonionUnitI.1 =
          - (-(u.2 * standardOctonionUnitI.1) - u.2 * standardOctonionUnitI.1) := by abel
      _ = 0 := by rw [h2'', neg_zero]
  have hsmul : (2 : ℝ) • (u.2 * standardOctonionUnitI.1) = 0 := by
    rw [two_smul ℝ]
    exact htwice
  rcases smul_eq_zero.mp hsmul with htwo | hmul
  · norm_num at htwo
  · exact (mul_eq_zero.mp hmul).resolve_right (by
      change (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) ≠ 0
      intro hunit
      have him := congrArg (fun z : ℍ[ℝ] => z.imI) hunit
      norm_num at him)

private theorem pure_eq_zero_of_commutators_standardOctonionUnits (u : RealOctonion)
    (hre : u.1.re = 0)
    (hi : u * standardOctonionUnitI - standardOctonionUnitI * u = 0)
    (hj : u * standardOctonionUnitJ - standardOctonionUnitJ * u = 0) : u = 0 := by
  have hu2 : u.2 = 0 := snd_eq_zero_of_commutator_standardOctonionUnitI u hi
  have hIfst := congrArg Prod.fst hi
  have hJfst := congrArg Prod.fst hj
  change (u * standardOctonionUnitI).1 - (standardOctonionUnitI * u).1 = 0 at hIfst
  change (u * standardOctonionUnitJ).1 - (standardOctonionUnitJ * u).1 = 0 at hJfst
  rw [mul_fst, mul_fst] at hIfst hJfst
  have hIzero : standardOctonionUnitI.2 = 0 := rfl
  have hJzero : standardOctonionUnitJ.2 = 0 := rfl
  have hIfst' : u.1 * standardOctonionUnitI.1 - standardOctonionUnitI.1 * u.1 = 0 := by
    simpa only [hIzero, hJzero, star_zero, zero_mul, mul_zero, sub_zero] using hIfst
  have hJfst' : u.1 * standardOctonionUnitJ.1 - standardOctonionUnitJ.1 * u.1 = 0 := by
    simpa only [hIzero, hJzero, star_zero, zero_mul, mul_zero, sub_zero] using hJfst
  apply ext
  · exact quaternion_eq_zero_of_re_eq_zero_of_commutators u.1 hre
      (by simpa [standardOctonionUnitI, standardQuaternionUnitI] using hIfst')
      (by simpa [standardOctonionUnitJ, standardQuaternionUnitJ] using hJfst')
  · exact hu2

private theorem anticommutator_commutator_of_square_scalar (u e : RealOctonion) (c : ℝ)
    (hsq : u * u = scalarEmbed c) :
    u * (u * e - e * u) + (u * e - e * u) * u = 0 := by
  calc
    u * (u * e - e * u) + (u * e - e * u) * u =
        u * (u * e) - u * (e * u) + (u * e) * u - (e * u) * u := by
          rw [mul_sub, sub_mul]
          abel
    _ = (u * u) * e - u * (e * u) + u * (e * u) - e * (u * u) := by
          rw [IsAlternative.mul_alternative_left, IsAlternative.mul_flexible,
            IsAlternative.mul_alternative_right]
    _ = (u * u) * e - e * (u * u) := by abel
    _ = scalarEmbed c * e - e * scalarEmbed c := by rw [hsq]
    _ = 0 := by rw [scalarEmbed_mul, mul_scalarEmbed]; abel

/-- If `Q_s(q)=0`, then `q - star s` is a kernel vector for `R_s - L_q`. -/
theorem kernel_q_sub_star_of_quadratic_eq_zero (s q : RealOctonion)
    (hquad : quadratic s q = 0) : resolventDifference s q (q - star s) = 0 := by
  have hnorm : star s * s = scalarEmbed (normSq s) := star_mul_self_eq_scalarEmbed s
  have htrace : q * (star s + s) = scalarEmbed (2 * s.1.re) * q := by
    rw [add_comm (star s) s, add_star_eq_scalarEmbed]
    rw [mul_scalarEmbed, scalarEmbed_mul]
  unfold quadratic at hquad
  unfold resolventDifference leftAction rightAction
  rw [sub_mul, mul_sub]
  calc
    q * s - star s * s - (q * q - q * star s) =
        -(q * q - q * (star s + s) + star s * s) := by
          rw [mul_add]
          abel
    _ = -(q * q - scalarEmbed (2 * s.1.re) * q + scalarEmbed (normSq s)) := by
          rw [htrace, hnorm]
    _ = 0 := by rw [hquad, neg_zero]

private theorem degenerate_sphere_kernel (s q : RealOctonion)
    (hant : q = star s) (hqnonreal : q - scalarEmbed q.1.re ≠ 0) :
    ∃ x : RealOctonion, x ≠ 0 ∧ resolventDifference s q x = 0 := by
  let a : ℝ := q.1.re
  let u := q - scalarEmbed a
  have hune : u ≠ 0 := by simpa [u, a] using hqnonreal
  have hure : u.1.re = 0 := by
    dsimp [u]
    change q.1.re - q.1.re = 0
    ring
  have hchar := quadratic_characteristic u
  have hsquare : u * u = scalarEmbed (-normSq u) := by
    rw [hure] at hchar
    have hsum : u * u + scalarEmbed (normSq u) = 0 := by
      simpa using hchar
    calc
      u * u = -scalarEmbed (normSq u) := eq_neg_of_add_eq_zero_left hsum
      _ = scalarEmbed (-normSq u) := (map_neg scalarEmbed _).symm
  by_cases hi : u * standardOctonionUnitI - standardOctonionUnitI * u = 0
  · by_cases hj : u * standardOctonionUnitJ - standardOctonionUnitJ * u = 0
    · exfalso
      apply hune
      exact pure_eq_zero_of_commutators_standardOctonionUnits u hure hi hj
    · refine ⟨u * standardOctonionUnitJ - standardOctonionUnitJ * u, hj, ?_⟩
      have hanti := anticommutator_commutator_of_square_scalar u standardOctonionUnitJ
        (-normSq u) hsquare
      have hu : u * (u * standardOctonionUnitJ - standardOctonionUnitJ * u) =
          -((u * standardOctonionUnitJ - standardOctonionUnitJ * u) * u) :=
        eq_neg_of_add_eq_zero_left hanti
      have hq : q = scalarEmbed a + u := by
        dsimp [u]
        abel
      have hstarq : star q = scalarEmbed a - u := by
        rw [star_eq_scalarEmbed_sub]
        have htwo : scalarEmbed (2 * a) = scalarEmbed a + scalarEmbed a := by
          rw [← map_add]
          congr 1
          ring
        rw [htwo]
        dsimp [u]
        abel
      have hqw : q * (u * standardOctonionUnitJ - standardOctonionUnitJ * u) =
          (u * standardOctonionUnitJ - standardOctonionUnitJ * u) * star q := by
        calc
          q * (u * standardOctonionUnitJ - standardOctonionUnitJ * u) =
              (scalarEmbed a + u) * (u * standardOctonionUnitJ - standardOctonionUnitJ * u) := by
                rw [hq]
          _ = scalarEmbed a * (u * standardOctonionUnitJ - standardOctonionUnitJ * u) +
              u * (u * standardOctonionUnitJ - standardOctonionUnitJ * u) := by rw [add_mul]
          _ = (u * standardOctonionUnitJ - standardOctonionUnitJ * u) * scalarEmbed a -
              (u * standardOctonionUnitJ - standardOctonionUnitJ * u) * u := by
                rw [scalarEmbed_mul, mul_scalarEmbed, hu]
                abel
          _ = (u * standardOctonionUnitJ - standardOctonionUnitJ * u) * (scalarEmbed a - u) :=
            (mul_sub _ _ _).symm
          _ = (u * standardOctonionUnitJ - standardOctonionUnitJ * u) * star q := by rw [hstarq]
      have hs : s = star q := by rw [hant, star_star]
      unfold resolventDifference leftAction rightAction
      rw [hs]
      exact sub_eq_zero.mpr hqw.symm
  · refine ⟨u * standardOctonionUnitI - standardOctonionUnitI * u, hi, ?_⟩
    have hanti := anticommutator_commutator_of_square_scalar u standardOctonionUnitI
      (-normSq u) hsquare
    have hu : u * (u * standardOctonionUnitI - standardOctonionUnitI * u) =
        -((u * standardOctonionUnitI - standardOctonionUnitI * u) * u) :=
      eq_neg_of_add_eq_zero_left hanti
    have hq : q = scalarEmbed a + u := by
      dsimp [u]
      abel
    have hstarq : star q = scalarEmbed a - u := by
      rw [star_eq_scalarEmbed_sub]
      have htwo : scalarEmbed (2 * a) = scalarEmbed a + scalarEmbed a := by
        rw [← map_add]
        congr 1
        ring
      rw [htwo]
      dsimp [u]
      abel
    have hqw : q * (u * standardOctonionUnitI - standardOctonionUnitI * u) =
        (u * standardOctonionUnitI - standardOctonionUnitI * u) * star q := by
      calc
        q * (u * standardOctonionUnitI - standardOctonionUnitI * u) =
            (scalarEmbed a + u) * (u * standardOctonionUnitI - standardOctonionUnitI * u) := by
              rw [hq]
        _ = scalarEmbed a * (u * standardOctonionUnitI - standardOctonionUnitI * u) +
            u * (u * standardOctonionUnitI - standardOctonionUnitI * u) := by rw [add_mul]
        _ = (u * standardOctonionUnitI - standardOctonionUnitI * u) * scalarEmbed a -
            (u * standardOctonionUnitI - standardOctonionUnitI * u) * u := by
              rw [scalarEmbed_mul, mul_scalarEmbed, hu]
              abel
        _ = (u * standardOctonionUnitI - standardOctonionUnitI * u) * (scalarEmbed a - u) :=
          (mul_sub _ _ _).symm
        _ = (u * standardOctonionUnitI - standardOctonionUnitI * u) * star q := by rw [hstarq]
    have hs : s = star q := by rw [hant, star_star]
    unfold resolventDifference leftAction rightAction
    rw [hs]
    exact sub_eq_zero.mpr hqw.symm

private theorem real_antipodal_kernel (s q : RealOctonion)
    (hant : q = star s) (hreal : q - scalarEmbed q.1.re = 0) :
    (1 : RealOctonion) ≠ 0 ∧ resolventDifference s q 1 = 0 := by
  let a : ℝ := q.1.re
  have hreal' : q - scalarEmbed a = 0 := by simpa [a] using hreal
  have hq : q = scalarEmbed a := sub_eq_zero.mp hreal'
  have hs : s = scalarEmbed a := by
    calc
      s = star q := by rw [hant, star_star]
      _ = star (scalarEmbed a) := congrArg star hq
      _ = scalarEmbed a := by
        apply ext <;> simp [scalarEmbed]
  constructor
  · intro hone
    have hfst := congrArg Prod.fst hone
    norm_num [scalarEmbed] at hfst
  · unfold resolventDifference leftAction rightAction
    rw [hs, hq, one_mul, mul_one, sub_self]

/-- Every point of the source conjugacy sphere produces a nonzero kernel vector for `R_s-L_q`. -/
theorem exists_nonzero_kernel_of_mem_conjugacySphere (s q : RealOctonion)
    (hmem : s ∈ conjugacySphere q) :
    ∃ x : RealOctonion, x ≠ 0 ∧ resolventDifference s q x = 0 := by
  have hquad : quadratic s q = 0 := (mem_conjugacySphere_iff_quadratic_eq_zero s q).mp hmem
  by_cases hqs : q = star s
  · by_cases hreal : q - scalarEmbed q.1.re = 0
    · exact ⟨1, real_antipodal_kernel s q hqs hreal⟩
    · exact degenerate_sphere_kernel s q hqs hreal
  · exact ⟨q - star s, sub_ne_zero.mpr hqs,
      kernel_q_sub_star_of_quadratic_eq_zero s q hquad⟩

/-- On the conjugacy sphere, the Sylvester difference is not injective. -/
theorem sylvesterDifferenceLinear_not_injective_of_mem_conjugacySphere
    (s q : RealOctonion) (hmem : s ∈ conjugacySphere q) :
    ¬ Function.Injective (sylvesterDifferenceLinear s q) := by
  intro hinj
  obtain ⟨x, hx, hkernel⟩ := exists_nonzero_kernel_of_mem_conjugacySphere s q hmem
  apply hx
  apply hinj
  change resolventDifference s q x = resolventDifference s q 0
  rw [hkernel]
  simp [resolventDifference, leftAction, rightAction]

/-- Lemma 8.5's exact real-linear invertibility classification. -/
theorem sylvesterDifferenceLinear_bijective_iff_not_mem_conjugacySphere (s q : RealOctonion) :
    Function.Bijective (sylvesterDifferenceLinear s q) ↔ s ∉ conjugacySphere q := by
  constructor
  · intro hbij hmem
    exact sylvesterDifferenceLinear_not_injective_of_mem_conjugacySphere s q hmem hbij.1
  · intro hsphere
    have hinj := sylvesterDifferenceLinear_injective_of_not_mem_conjugacySphere s q hsphere
    exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

/-- The determinant zero locus in Lemma 8.5, expressed without a chosen coordinate basis. -/
theorem sylvesterDifferenceLinear_det_eq_zero_iff_mem_conjugacySphere (s q : RealOctonion) :
    LinearMap.det (sylvesterDifferenceLinear s q) = 0 ↔ s ∈ conjugacySphere q := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
  constructor
  · intro hker
    by_contra hnot
    exact hker (LinearMap.ker_eq_bot.mpr
      (sylvesterDifferenceLinear_injective_of_not_mem_conjugacySphere s q hnot))
  · intro hmem hker
    exact sylvesterDifferenceLinear_not_injective_of_mem_conjugacySphere s q hmem
      (LinearMap.ker_eq_bot.mp hker)

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
