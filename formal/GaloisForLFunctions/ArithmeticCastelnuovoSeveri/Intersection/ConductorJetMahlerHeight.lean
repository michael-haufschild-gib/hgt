import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorJetHeightLimit
import Mathlib.NumberTheory.MahlerMeasure
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.ThickenedArithmeticIntersections

/-!
# Joint finite-place and boundary height of the rational jet section

Pull the interpolant back along a polynomial graph in the unit bidisk.
Jensen's formula pays the integer content of the denominator from its
mean log modulus. The same subquadratic allowance thus controls both the
finite-place denominator and the mean positive log of the unscaled section.
On every sufficiently large torsion orbit the corresponding finite term
is the logarithm of the cardinality of an integral intersection ring.
-/

noncomputable section
open Finset Polynomial Real Filter Topology
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Restrict the two-variable polynomial to the graph of Y = y(T). -/
def conductorJetSlice (y : ℂ[X]) : Polynomial ℤ[X] →+* ℂ[X] :=
  eval₂RingHom (mapRingHom (Int.castRingHom ℂ)) y

/-- Integer content of the clearing denominator and mean positive log modulus
of the rational section on the graph Y = y(T), in the same logarithmic units. -/
def conductorJetBoundaryHeight (D : ℤ[X]) (F : Polynomial ℤ[X]) (y : ℂ[X]) : ℝ :=
  circleAverage (fun z => posLog ‖(conductorJetSlice y F).eval z /
    (D.map (Int.castRingHom ℂ)).eval z‖) 0 1 + log (verticalContent D : ℝ)

private theorem content_le_mahler {D : ℤ[X]} (hD : D ≠ 0) :
    (verticalContent D : ℝ) ≤ (D.map (Int.castRingHom ℂ)).mahlerMeasure := by
  apply le_trans _ (D.map (Int.castRingHom ℂ)).leadingCoeff_le_mahlerMeasure
  rw [leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int, Int.coe_castRingHom]
  change (D.content.natAbs : ℝ) ≤ _
  rw [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have hd := Int.natAbs_dvd_natAbs.mpr (content_dvd_coeff (p := D) D.natDegree)
  change D.content.natAbs ∣ D.leadingCoeff.natAbs at hd
  have h := Nat.le_of_dvd (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hD)) hd
  simpa only [Nat.cast_natAbs, Int.cast_abs] using (show (D.content.natAbs:ℝ) ≤ D.leadingCoeff.natAbs by exact_mod_cast h)

private theorem posLog_div_bound {v d : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hv : ‖v‖ ≤ exp L) (hd : ‖d‖ ≤ exp L) : posLog ‖v / d‖ ≤ L - log ‖d‖ := by
  have log_le {z : ℂ} (hz : ‖z‖ ≤ exp L) : log ‖z‖ ≤ L := by
    by_cases he : z = 0
    · simpa [he] using hL
    · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr he)).mpr hz
  have h0 := sub_nonneg.mpr (log_le hd)
  change max 0 (log ‖v/d‖) ≤ _
  apply max_le h0
  by_cases hd0 : d = 0
  · simpa [hd0] using h0
  by_cases hv0 : v = 0
  · simpa [hv0] using h0
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hv0) (norm_ne_zero_iff.mpr hd0)]
  exact sub_le_sub_right (log_le hv) _

private theorem rational_circle_height {D : ℤ[X]} (hD : D ≠ 0) (P : ℂ[X]) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → max ‖(D.map (Int.castRingHom ℂ)).eval z‖ ‖P.eval z‖ ≤ exp L) :
    Real.circleAverage (fun z => posLog ‖P.eval z / (D.map (Int.castRingHom ℂ)).eval z‖) 0 1 +
      log (verticalContent D : ℝ) ≤ L := by
  let Q := D.map (Int.castRingHom ℂ)
  have hq : CircleIntegrable (fun z => log ‖Q.eval z‖) 0 1 :=
    (analyticOnNhd_id.aeval_polynomial Q).meromorphicOn.circleIntegrable_log_norm
  have hrat : CircleIntegrable (fun z => posLog ‖P.eval z / Q.eval z‖) 0 1 :=
    ((analyticOnNhd_id.aeval_polynomial P).meromorphicOn.div
      (analyticOnNhd_id.aeval_polynomial Q).meromorphicOn).circleIntegrable_posLog_norm
  have hm := circleAverage_mono hrat ((circleIntegrable_const L 0 1).sub hq) fun z hz => by
    have hz' : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    exact posLog_div_bound hL ((le_max_right _ _).trans (hb z hz')) ((le_max_left _ _).trans (hb z hz'))
  rw [circleAverage_sub (circleIntegrable_const L 0 1) hq, circleAverage_const, ← logMahlerMeasure_def,
    logMahlerMeasure_eq_log_MahlerMeasure] at hm
  have hd : 0 < (verticalContent D:ℝ) := by
    change 0 < (D.content.natAbs:ℝ)
    exact_mod_cast Int.natAbs_pos.mpr (mt content_eq_zero_iff.mp hD)
  linarith only [hm, Real.log_le_log hd (content_le_mahler hD)]

open RenormalizedIntersectionArithmeticCounts

/-- Height of the specialized quotient over a primitive torsion orbit.
Its finite term counts the actual residue ring ℤ[T]/(Φ_q,D). -/
def conductorJetTorsionHeight (D : ℤ[X]) (F : Polynomial ℤ[X]) (y : ℂ[X]) (q : ℕ) : ℝ :=
  (arithmeticIntersectionHeight (cyclotomic q ℤ) D +
    ∑ z ∈ primitiveRoots q ℂ, posLog ‖(conductorJetSlice y F).eval z /
      (D.map (Int.castRingHom ℂ)).eval z‖) / (primitiveRoots q ℂ).card

private theorem cyclotomic_resultant_graph (D : ℤ[X]) {q : ℕ} (hq : 0 < q) :
    (((cyclotomic q ℤ).resultant D : ℤ) : ℂ) =
      ∏ z ∈ primitiveRoots q ℂ, (D.map (Int.castRingHom ℂ)).eval z := by
  letI : NeZero (q:ℂ) := ⟨by exact_mod_cast hq.ne'⟩
  have he := resultant_map_map (cyclotomic q ℤ) D (cyclotomic q ℤ).natDegree D.natDegree
    (Int.castRingHom ℂ)
  rw [map_cyclotomic_int] at he
  have hc : (((cyclotomic q ℤ).resultant D : ℤ) : ℂ) =
      resultant (cyclotomic q ℂ) (D.map (Int.castRingHom ℂ)) (cyclotomic q ℂ).natDegree D.natDegree := by
    simpa only [natDegree_cyclotomic,Int.coe_castRingHom] using he.symm
  rw [hc,resultant_eq_prod_eval _ _ _ natDegree_map_le (IsAlgClosed.splits _),
    (cyclotomic.monic q ℂ).leadingCoeff,one_pow,one_mul,cyclotomic.roots_eq_primitiveRoots_val]
  rfl

/-- At every sufficiently large torsion order the denominator is invertible
on the whole orbit. Its residue cardinality and the mean positive log of
the rational section share the same bidisk log bound. -/
theorem conductorJet_torsion_specialization (D : ℤ[X]) (F : Polynomial ℤ[X]) (hD : D ≠ 0)
    {L : ℝ} (hL : 0 ≤ L) :
    ∀ᶠ q : ℕ in atTop,
      (∀ z ∈ primitiveRoots q ℂ, (D.map (Int.castRingHom ℂ)).eval z ≠ 0) ∧
      ∀ y : ℂ[X], (∀ z ∈ primitiveRoots q ℂ, max ‖(D.map (Int.castRingHom ℂ)).eval z‖
        ‖(conductorJetSlice y F).eval z‖ ≤ exp L) → conductorJetTorsionHeight D F y q ≤ L := by
  classical
  let Q := D.map (Int.castRingHom ℂ)
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hD
  filter_upwards [eventually_gt_atTop (∑ z ∈ Q.roots.toFinset, orderOf z)] with q hq
  have hq0 : 0 < q := (Nat.zero_le _).trans_lt hq
  have hn (z : ℂ) (hz : z ∈ primitiveRoots q ℂ) : Q.eval z ≠ 0 := by
    intro he
    have hroot := Multiset.mem_toFinset.mpr ((mem_roots hQ).mpr he)
    have horder := (mem_primitiveRoots hq0).mp hz
    have h := single_le_sum (fun w _ => Nat.zero_le (orderOf w)) hroot
    exact (not_le_of_gt hq) (horder.eq_orderOf.trans_le h)
  refine ⟨hn,fun y hb => ?_⟩
  have he := cyclotomic_resultant_graph D hq0
  have hres : (cyclotomic q ℤ).resultant D ≠ 0 := by
    intro h
    rw [h,Int.cast_zero] at he
    exact (prod_ne_zero_iff.mpr hn) he.symm
  have hcount : arithmeticIntersectionHeight (cyclotomic q ℤ) D =
      ∑ z ∈ primitiveRoots q ℂ, log ‖Q.eval z‖ := by
    rw [arithmeticIntersectionHeight_archimedean (cyclotomic.monic _ _) hres, ← Complex.norm_intCast,
      he,norm_prod,Real.log_prod (fun z hz => norm_ne_zero_iff.mpr (hn z hz))]
  have hcard : 0 < (primitiveRoots q ℂ).card :=
    card_pos.mpr ⟨_, (mem_primitiveRoots hq0).mpr (Complex.isPrimitiveRoot_exp q hq0.ne')⟩
  unfold conductorJetTorsionHeight
  rw [div_le_iff₀ (Nat.cast_pos.mpr hcard),hcount,← sum_add_distrib]
  have hterm (z) (hz : z ∈ primitiveRoots q ℂ) :
      log ‖Q.eval z‖ + posLog ‖(conductorJetSlice y F).eval z / Q.eval z‖ ≤ L := by
    have h := posLog_div_bound hL ((le_max_right _ _).trans (hb z hz)) ((le_max_left _ _).trans (hb z hz))
    linarith only [h]
  simpa only [sum_const,nsmul_eq_mul,mul_comm L] using sum_le_sum hterm

/-- Every bounded set of prescribed jets admits one integral numerator and
denominator. Their quotient has the prescribed jets, with the finite
denominator and mean boundary growth paid from the same allowance. -/
theorem conductorMeshJetSection_jointHeight (B H m : ℕ) (data : ℕ → Polynomial ℤ[X]) :
    let S := Icc (max 1 m.sqrt) (B*m.sqrt)
    let h := meshJetOrder H m
    ∃ (D : ℤ[X]) (F : Polynomial ℤ[X]), D ≠ 0 ∧
      (∀ j ∈ S, (X - C (conductorGraph j))^h ∣ F - C D * data j) ∧
      ∀ y : ℂ[X], (∀ z : ℂ, ‖z‖ = 1 → ‖y.eval z‖ ≤ 1) → (∀ j ∈ S, ∀ z : ℂ, ‖z‖ = 1 → ‖(conductorJetSlice y (data j)).eval z‖ ≤ 1) →
        conductorJetBoundaryHeight D F y ≤ meshJetLogBound B H m ∧
          ∀ᶠ q : ℕ in atTop, conductorJetTorsionHeight D F y q ≤ meshJetLogBound B H m := by
  intro S h
  obtain ⟨D,F,hD,hjet,_,hbound⟩ := conductorMeshJetSections B H m data
  refine ⟨D,F,hD,hjet,fun y hy hdata => ?_⟩
  have hL : 0 ≤ meshJetLogBound B H m := by
    unfold meshJetLogBound
    apply mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg _)
    nlinarith only [sq_nonneg (((B+1)*m.sqrt:ℕ):ℝ)]
  have hb (z : ℂ) (hz : ‖z‖ = 1) : max ‖(D.map (Int.castRingHom ℂ)).eval z‖
      ‖(conductorJetSlice y F).eval z‖ ≤ exp (meshJetLogBound B H m) := by
    let e := (evalRingHom z).comp (conductorJetSlice y)
    have hY : ‖e X‖ ≤ 1 := by simpa [e,conductorJetSlice] using hy z hz
    have hT : ‖e (C X)‖ ≤ 1 := by simpa [e,conductorJetSlice] using hz.le
    simpa [e,conductorJetSlice] using hbound e hY hT (fun j hj => hdata j hj z hz)
  refine ⟨rational_circle_height hD _ hL hb, ?_⟩
  filter_upwards [conductorJet_torsion_specialization D F hD hL, eventually_ge_atTop 1] with q hq hq0
  exact hq.2 y fun z hz => hb z (Complex.norm_eq_one_of_pow_eq_one
    ((mem_primitiveRoots hq0).mp hz).pow_eq_one (Nat.ne_of_gt hq0))

/-- A nonempty family of marked branches has a nonzero interpolant: it is
one on the marked thickenings and zero on every other thickening after division
by D. The joint height fits every positive quadratic allowance. -/
private theorem anchoredSections (B H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (A : Finset ℕ) (r : ℕ),
      let S := Icc (max 1 m.sqrt) (B*m.sqrt)
      r ∈ S → r ∈ A →
      ∃ (D : ℤ[X]) (F : Polynomial ℤ[X]), D ≠ 0 ∧ F ≠ 0 ∧
        (∀ j ∈ S, (X - C (conductorGraph j))^(meshJetOrder H m) ∣ F - (if j ∈ A then C D else 0)) ∧
        ∀ y : ℂ[X], (∀ z : ℂ, ‖z‖ = 1 → ‖y.eval z‖ ≤ 1) →
          conductorJetBoundaryHeight D F y < ε*(m:ℝ)^2 ∧
          ∀ᶠ q : ℕ in atTop, conductorJetTorsionHeight D F y q < ε*(m:ℝ)^2 := by
  filter_upwards [(meshJetLogBound_subquadratic B H).eventually_lt_const hε,
      eventually_ge_atTop 1] with m hm hm1
  intro A r S hr hA
  let data := fun j : ℕ => if j ∈ A then (1 : Polynomial ℤ[X]) else 0
  obtain ⟨D,F,hD,hjet,hbound⟩ := conductorMeshJetSection_jointHeight B H m data
  have hj (j) (hj : j ∈ S) : (X - C (conductorGraph j))^(meshJetOrder H m) ∣
      F - (if j ∈ A then C D else 0) := by
    by_cases he : j ∈ A <;> simpa [data, he] using hjet j hj
  have hr' := hj r hr
  rw [if_pos hA] at hr'
  have hlin : X - C (conductorGraph r) ∣ F - C D :=
    (dvd_pow_self _ (by simp [meshJetOrder])).trans hr'
  have hv := dvd_iff_isRoot.mp hlin
  change (F - C D).eval (conductorGraph r) = 0 at hv
  have hF : F ≠ 0 := by
    intro h
    exact hD (by simpa [h] using hv)
  refine ⟨D,F,hD,hF,hj,fun y hy => ?_⟩
  have hb := hbound y hy (fun j _ z _ => show ‖(conductorJetSlice y (data j)).eval z‖ ≤ 1 by
    by_cases he : j ∈ A <;> simp [data,he])
  have hlt := (div_lt_iff₀ (by positivity : 0 < (m:ℝ)^2)).mp hm
  exact ⟨hb.1.trans_lt hlt, hb.2.mono fun _ h => h.trans_lt hlt⟩

/-- Every zero/one assignment on all conductor thickenings has a nonzero
section for every positive quadratic allowance. A further branch fixes the
value one even when all of the prescribed jets vanish. -/
theorem conductorMesh_markedSections (B H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ A : Finset ℕ,
      ∃ (D : ℤ[X]) (F : Polynomial ℤ[X]), D ≠ 0 ∧ F ≠ 0 ∧
        (∀ j ∈ Icc (max 1 m.sqrt) (B*m.sqrt), (X - C (conductorGraph j))^(meshJetOrder H m) ∣
          F - (if j ∈ A then C D else 0)) ∧
        ∀ y : ℂ[X], (∀ z : ℂ, ‖z‖ = 1 → ‖y.eval z‖ ≤ 1) →
          conductorJetBoundaryHeight D F y < ε*(m:ℝ)^2 ∧
          ∀ᶠ q : ℕ in atTop, conductorJetTorsionHeight D F y q < ε*(m:ℝ)^2 := by
  filter_upwards [anchoredSections (B+1) H hε, eventually_ge_atTop 1] with m hm hm1
  intro A
  let r := (B+1)*m.sqrt
  have hm0 := Nat.sqrt_pos.mpr hm1
  have hl : B*m.sqrt < r := by dsimp [r]; rw [Nat.add_mul, Nat.one_mul]; omega
  have hr : max 1 m.sqrt ≤ r := by
    rw [max_eq_right hm0]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  obtain ⟨D,F,hD,hF,hj,hb⟩ := hm (insert r A) r (mem_Icc.mpr ⟨hr, le_rfl⟩) (mem_insert_self _ _)
  refine ⟨D,F,hD,hF,fun j hi => ?_,hb⟩
  have hjr := (mem_Icc.mp hi).2.trans_lt hl
  simpa only [mem_insert, hjr.ne, false_or] using
    hj j (mem_Icc.mpr ⟨(mem_Icc.mp hi).1,hjr.le⟩)

#print axioms conductorJet_torsion_specialization
#print axioms conductorMesh_markedSections
#print axioms conductorMeshJetSection_jointHeight

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
