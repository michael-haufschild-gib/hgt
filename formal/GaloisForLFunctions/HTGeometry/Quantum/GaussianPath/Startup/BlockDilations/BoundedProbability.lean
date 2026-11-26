import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.FiniteTransfer
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.DrawConstraints
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PeriodicPackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.BoundaryEnergy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.MassRegularity

/-! # Fixed-date Gaussian circuit probability from physical packet masses -/

open MeasureTheory ProbabilityTheory Finset Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {n : ℕ}

private theorem weight_antitone {g j b : ℕ} (hg : g≤j) (hj : j≤b) :
    3^j*4^(b-j)≤3^g*4^(b-g) := by
  have h₁ : g+(j-g)=j := by omega
  have h₂ : (j-g)+(b-j)=b-g := by omega
  calc
    _ = (3^g*3^(j-g))*4^(b-j) := by rw [←pow_add,h₁]
    _ ≤ (3^g*4^(j-g))*4^(b-j) := Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _))
    _ = _ := by rw [Nat.mul_assoc,←pow_add,h₂]

/-- All physical packet choices use only couplings in the same set of
seam neighbourhoods to bound their comparison errors. -/
theorem periodic_boundary (L : ℕ) (x : PathLabel n→ℝ) (y : Fin ((n+1)/L+1)→Bool) :
    let C := SpectralGapMass.Bulk.PeriodicCuts.labels (n:=n) L none
    let u : PathShell n := WithLp.toLp 2 x
    boundaryMass u (selectedLabels (periodicPacket L) y)≤84*energyOn (seamNeighbourhood C) x := by
  intro C u
  simpa only [u,restricted_energy] using
    boundaryMass_le_seam (selectedLabels (periodicPacket L) y) C u
      (fun _ hq _ hl hi => outside_word_crosses L y hq hl hi)

/-- A finite Gaussian bound at the actual physical date. The event
requires a minimum longitudinal mass, a maximum total energy and a
maximum seam energy, all measured on the original draw. -/
theorem bounded_cheap_mass (L r s g : ℕ) (hL : 0<L) {t a : ℝ} (ht : 0≤t) (ha : 0≤a)
    (e F E B : ℝ) {m C : ℝ} (hm : 0 ≤ m) (hC : 0 < C) :
    let b := (n+1)/L+1
    let T := seamNeighbourhood (SpectralGapMass.Bulk.PeriodicCuts.labels (n:=n) L none)
    let δ := t^2*a*(84*B)
    let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
    π≤2*(t*a)*m →
    2*(e+δ)+(t*a)*C*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1 →
    b*m+g*(sqrt L*C)+sqrt L/C*E < F/(1+a) →
    μ.real (affordableDraw n s e t ∩ drawBounds T F E B)*(2:ℝ)^b ≤
      (1+a)^Fintype.card (PathLabel n)*((3^g*4^(b-g):ℕ):ℝ)/(2:ℝ)^(b-2*s/(r+1)) := by
  classical
  intro b T δ μ hcross htest hfield
  let R := periodicPacket (n:=n) L
  let A := selectedLabels R
  let Z := affordableDraw n s e t ∩ drawBounds T F E B
  let N : ℕ := 2^(b-2*s/(r+1))
  let M : ℝ := ((3^g*4^(b-g):ℕ):ℝ)/N
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hM : 0≤M := div_nonneg (Nat.cast_nonneg _) hN.le
  have hZ : MeasurableSet Z := (measurable_affordableDraw ..).inter (measurable_drawBounds ..)
  have ha' : 1≤1+a := le_add_of_nonneg_right ha
  have hcount (x : PathLabel n→ℝ) :
      ((univ.filter fun j => expand (A j) (1+a) x∈Z).card:ℝ)≤M := by
    let Q := univ.filter fun j => expand (A j) (1+a) x∈Z
    by_cases hQ : Q.Nonempty
    · obtain ⟨j,hj⟩ := hQ
      have hbounds := drawBounds_precursor (A j) T ha' F E B x (mem_filter.mp hj).2.2
      obtain ⟨⟨hlong,henergy⟩,hseam⟩ := hbounds
      let u : PathShell n := WithLp.toLp 2 x
      let d := univ.sup' univ_nonempty (fun j => t^2*a*boundaryMass u (A j))
      let G := univ.filter fun i => regularPacket (R i) u (t*a) (e+d) r
      have hd : d≤δ := by
        apply Finset.sup'_le
        intro j _
        exact mul_le_mul_of_nonneg_left ((periodic_boundary L x j).trans
          (mul_le_mul_of_nonneg_left hseam (by norm_num))) (mul_nonneg (sq_nonneg t) ha)
      have hsmall : 2*(e+d)+(t*a)*C*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1 :=
        lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hd) zero_le_two) le_rfl) htest
      have hs := regular_mass_bound R (periodic_disjoint L) u L r (periodic_card hL) hm hC
        (mul_nonneg ht ha) hcross hsmall
      change (∑ i, longitudinal (periodicPacket L i) u) ≤
        Fintype.card (Fin b)*m+G.card*(sqrt L*C)+sqrt L/C*‖u‖^2 at hs
      rw [Fintype.card_fin,periodic_longitudinal,total_energy] at hs
      have hg : g≤G.card := by
        by_contra! hn
        have hmass := hs.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr hn.le) (mul_nonneg (sqrt_nonneg _) hC.le)))
          (mul_le_mul_of_nonneg_left henergy (div_nonneg (sqrt_nonneg _) hC.le)))
        exact hfield.not_ge (hlong.trans hmass)
      let P := univ.filter fun j => HasProjectiveCircuitApproximation (n+2) e s
        (unitaryEvolution (pathHamiltonian (dilateShell (A j) a u)) t)
      have hsub : Q⊆P := by
        intro j hj
        have he := (mem_filter.mp hj).2.1
        change HasProjectiveCircuitApproximation (n+2) e s
          (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 (expand (A j) (1+a) x))) t) at he
        rw [expand_eq_dilateShell] at he
        exact mem_filter.mpr ⟨mem_univ _,he⟩
      have hp := physical_pattern_count R (periodic_disjoint L) u ht ha e r s
      simp only [Fintype.card_fin] at hp
      change P.card*N≤3^G.card*4^(b-G.card) at hp
      have hb := (Nat.mul_le_mul_right N (card_le_card hsub)).trans
        (hp.trans (weight_antitone hg (G.card_le_univ.trans_eq (Fintype.card_fin _))))
      apply (le_div_iff₀ hN).mpr
      exact_mod_cast hb
    · rw [show (univ.filter fun j => expand (A j) (1+a) x∈Z)=∅ from not_nonempty_iff_eq_empty.mp hQ,
        card_empty,Nat.cast_zero]
      exact hM
  have h := gaussian_pattern_cap A ha' hZ M hM (fun x => by
    apply le_trans _ (hcount x)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro j hj
    simpa only [mem_filter,mem_univ,true_and] using hj)
  rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at h
  simpa only [M,N,Nat.cast_pow,Nat.cast_ofNat,mul_div_assoc] using h

#print axioms periodic_boundary
#print axioms bounded_cheap_mass
end
end GaloisForLFunctions.HTGeometry.BlockDilations
