import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.Baseline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.WeakBoundary
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.SitePartition
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.MassRegularity

/-! # Circuit counts on an arbitrary partition with uniformly weak seams -/

open MeasureTheory Finset Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

private theorem fewer_regular {g j b : ℕ} (hg : g≤j) (hj : j≤b) :
    3^j*4^(b-j)≤3^g*4^(b-g) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hg
  have hs : k+(b-(g+k))=b-g := by omega
  rw [pow_add,mul_assoc,←hs,pow_add]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _))

/-- One successful pattern supplies a common baseline with weak cut
coefficients. The packet tests on this baseline constrain every other
successful pattern, even though the partition was selected from the draw. -/
theorem weak_partition_count (owner : Fin (n+2)→I) (L r s g : ℕ)
    (hL : ∀ i, (sites owner i).card≤L) {t a w R : ℝ} (ht : 0≤t) (ha : 0≤a)
    (hw : 0≤w) (hR : 0≤R) (e F E : ℝ) {m C : ℝ} (hm : 0≤m) (hC : 0<C) :
    open Classical in
    let A := selectedLabels (sites owner)
    let T := cutLabels owner
    let b := Fintype.card I
    let δ := t^2*a*(84*(T.card:ℝ)*w*R)
    π≤2*(t*a)*m → 2*(e+δ)+(t*a)*C*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1 →
    b*m+g*(sqrt L*C)+sqrt L/C*E<F/(1+a) →
    ∀ z : PathLabel n→ℝ,
    let Z := affordableDraw n s e t ∩ cutBounds T F E w R
    (univ.filter fun j => expand (T∪A j) (1+a) z∈Z).card*2^(b-2*s/(r+1))≤3^g*4^(b-g) := by
  classical
  intro A T b δ hcross htest hfield z Z
  let Q := univ.filter fun j => expand (T∪A j) (1+a) z∈Z
  by_cases hQ : Q.Nonempty
  · let v := expand T (1+a) z
    let u : PathShell n := WithLp.toLp 2 v
    have hex (j : I→Bool) : expand (T∪A j) (1+a) z=expand (A j) (1+a) v :=
      expand_disjoint T _ (internal_disjoint_cut owner j) _ _
    obtain ⟨j,hj⟩ := hQ
    have hbnd := (mem_filter.mp hj).2.2
    rw [hex j] at hbnd
    have hb := cutBounds_precursor _ _ (le_add_of_nonneg_right ha) F E w R v hbnd
    let d := univ.sup' univ_nonempty (fun j => t^2*a*boundaryMass u (A j))
    have hd : d≤δ := by
      apply Finset.sup'_le
      intro y _
      exact mul_le_mul_of_nonneg_left
        (boundary_from_weak_cuts _ T u (fun _ hq _ hl h => outside_bond owner y hq hl h)
          hw hR hb.1.2 (fun l _ => hb.2 l)) (mul_nonneg (sq_nonneg _) ha)
    let G := univ.filter fun i => regularPacket (sites owner i) u (t*a) (e+d) r
    have hsmall := lt_of_le_of_lt (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl e) hd) zero_le_two) le_rfl) htest
    have hs := regular_mass_bound (sites owner) (sites_disjoint owner) u L r hL hm hC
      (mul_nonneg ht ha) hcross hsmall
    change (∑ i, longitudinal (sites owner i) u) ≤ b*m+G.card*(sqrt L*C)+sqrt L/C*‖u‖^2 at hs
    rw [sites_longitudinal,total_energy] at hs
    have hg : g≤G.card := by
      by_contra! hn
      have hmass := hs.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hn.le) (mul_nonneg (sqrt_nonneg _) hC.le)))
        (mul_le_mul_of_nonneg_left hb.1.1.1.2 (div_nonneg (sqrt_nonneg _) hC.le)))
      exact hfield.not_ge (hb.1.1.1.1.trans hmass)
    let P := univ.filter fun y => HasProjectiveCircuitApproximation (n+2) e s
      (unitaryEvolution (pathHamiltonian (dilateShell (A y) a u)) t)
    have hsub : Q⊆P := by
      intro y hy
      have h := (mem_filter.mp hy).2.1
      rw [hex y] at h
      change HasProjectiveCircuitApproximation (n+2) e s
        (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 (expand (A y) (1+a) v))) t) at h
      rw [expand_eq_dilateShell] at h
      exact mem_filter.mpr ⟨mem_univ _,h⟩
    have hp := physical_pattern_count (sites owner) (sites_disjoint owner) u ht ha e r s
    change P.card*2^(b-2*s/(r+1))≤3^G.card*4^(b-G.card) at hp
    exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans
      (hp.trans (fewer_regular hg (card_le_univ _)))
  · rw [show (univ.filter fun j => expand (T∪A j) (1+a) z∈Z)=∅ from not_nonempty_iff_eq_empty.mp hQ]
    simp only [card_empty,zero_mul,Nat.zero_le]

#print axioms weak_partition_count
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
