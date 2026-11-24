import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.CutPackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.ArcCover
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Density

/-! # Energy and phase coverage on a frozen Gaussian chain -/

open Finset Matrix Set Real MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
open WeakBonds ThermodynamicEdges
noncomputable section

/-- Almost surely the entire energy interval lies within O(√log N)
of the physical spectrum, including energies arbitrarily close to its edges. -/
theorem gaussian_energy_cover :
    ∃ B : ℝ, 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H := shellOperator (pathPauliDisorderShell ω n)
      ∀ y ∈ Icc (lower H) (upper H), ∃ i,
        |H.2.isHermitian.eigenvalues i-y| ≤ 42*sqrt (log (B*((n+2 : ℕ):ℝ))) := by
  obtain ⟨B,hB,hh⟩ := gaussian_subset_mass
  refine ⟨B,hB,?_⟩
  filter_upwards [hh] with ω hw
  filter_upwards [hw] with n hn
  intro H
  let u := pathPauliDisorderShell ω n
  let r := sqrt (log (B*((n+2 : ℕ):ℝ)))
  have h (l : PathLabel n) : |u l| ≤ 2*r := by
    have hs := hn {l} (singleton_nonempty _)
    simp only [sum_singleton,Finset.card_singleton,Nat.cast_one,one_pow,mul_one,div_one] at hs
    change |u l|^2 ≤ 4*log (B*((n+2 : ℕ):ℝ)) at hs
    have hlog : 0 ≤ log (B*((n+2 : ℕ):ℝ)) := by nlinarith only [hs,sq_nonneg |u l|]
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg zero_le_two (sqrt_nonneg _))).mp
    rw [mul_pow,sq_sqrt hlog]
    exact hs.trans_eq (by ring)
  have hsite (i : Fin (n+2)) : ‖onsiteAt u i‖ ≤ (3:ℝ)*(2*r) := by
    apply (norm_sum_le _ _).trans
    calc _ ≤ ∑ _ : Fin 3, 2*r := Finset.sum_le_sum fun q _ => by
               simpa only [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
                 using h (Sum.inl (i,q))
         _ = _ := by norm_num [nsmul_eq_mul]
  have hedge (i : Fin (n+1)) : ‖edgePart u i‖ ≤ (9:ℝ)*(2*r) := by
    apply (norm_sum_le _ _).trans
    calc _ ≤ ∑ _ : Fin 3 × Fin 3, 2*r := Finset.sum_le_sum fun q _ => by
               simpa only [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
                 using h (Sum.inr (i,q))
         _ = _ := by norm_num [nsmul_eq_mul]
  intro y hy
  obtain ⟨i,hi⟩ := path_energy_mesh u (by dsimp only [r]; positivity) (by dsimp only [r]; positivity) hsite hedge y hy
  exact ⟨i,hi.trans_eq (by dsimp only [r]; ring)⟩

/-- The energy covering radius is sublinear in the spin count. -/
theorem normalized_mesh {B : ℝ} (hB : 0<B) :
    Tendsto (fun n : ℕ => 42*sqrt (log (B*((n+2 : ℕ):ℝ)))/((n+2 : ℕ):ℝ)) atTop (𝓝 0) := by
  let N (n : ℕ) : ℝ := (n+2 : ℕ)
  have h : Tendsto (fun n => B/N n) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat B).comp (tendsto_add_atTop_nat 2)
  have hu : Tendsto (fun n => 42*sqrt (B/N n)) atTop (𝓝 0) := by
    simpa only [sqrt_zero,mul_zero] using h.sqrt.const_mul 42
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun n => by positivity
  filter_upwards with n
  have hN : 0<N n := by dsimp [N]; positivity
  change 42*sqrt (log (B*N n))/N n ≤ 42*sqrt (B/N n)
  have hh := (log_le_sub_one_of_pos (mul_pos hB hN)).trans (sub_le_self _ zero_le_one)
  have hr : sqrt (log (B*N n)) ≤ sqrt (B/N n)*N n := by
    apply sqrt_le_iff.mpr
    refine ⟨mul_nonneg (sqrt_nonneg _) hN.le,?_⟩
    rw [mul_pow,sq_sqrt (div_nonneg hB.le hN.le)]
    exact hh.trans_eq (by field_simp)
  apply (div_le_iff₀ hN).mpr
  linarith only [hr]

/-- Multiplying the energies by a positive time transports a real mesh
to an angular mesh until the missing arc closes. -/
theorem physical_arc_bounds {N : ℕ} (H : EnergyOperator (Fin N→Bool)) {q : ℝ}
    (hc : ∀ y ∈ Icc (lower H) (upper H), ∃ i, |H.2.isHermitian.eigenvalues i-y| ≤ q)
    {t : ℝ} (ht : 0 ≤ t) :
    min (t*circuitHamiltonianSpectralWidth H) (2*π-2*t*q) ≤ orbitSpectralEnclosingArcLength H t ∧
    orbitSpectralEnclosingArcLength H t ≤ min (t*circuitHamiltonianSpectralWidth H) (2*π) := by
  rcases ht.eq_or_lt with h|ht
  · subst t
    rw [initial_arc H le_rfl (by simpa only [zero_mul] using pi_pos.le)]
    simp only [zero_mul,mul_zero,sub_zero,min_eq_left two_pi_pos.le,le_rfl,and_self]
  let E := H.2.isHermitian.eigenvalues
  let θ (j) := -(t*E j)
  obtain ⟨a,_,ha⟩ := exists_mem_eq_sup' univ_nonempty E
  obtain ⟨b,_,hb⟩ := exists_mem_eq_inf' univ_nonempty E
  have hx : upper H=E a := ha
  have hn : lower H=E b := hb
  have hspan : θ b-θ a=t*circuitHamiltonianSpectralWidth H := by
    change -(t*E b)- -(t*E a)=t*(univ.sup' _ E-univ.inf' _ E)
    rw [ha,hb]; ring
  have he₁ (i) : E i ≤ E a := (le_sup' E (mem_univ i)).trans_eq ha
  have he₂ (i) : E b ≤ E i := hb.symm.le.trans (inf'_le E (mem_univ i))
  have hm : ∀ y∈Icc (θ a) (θ b), ∃ i, |θ i-y| ≤ t*q := by
    intro y hy
    have hl : lower H ≤ -y/t := (le_div_iff₀ ht).mpr (by
      rw [hn]; linarith only [show y ≤ -(t*E b) from hy.2])
    have hu : -y/t ≤ upper H := (div_le_iff₀ ht).mpr (by
      rw [hx]; linarith only [show -(t*E a) ≤ y from hy.1])
    obtain ⟨i,hi⟩ := hc _ ⟨hl,hu⟩
    refine ⟨i,?_⟩
    have hr : θ i-y= -(t*(E i-(-y/t))) := by dsimp only [θ]; field_simp; ring
    rw [hr,abs_neg,abs_mul,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hi ht.le
  have hh := arc_of_interval_cover θ a b (fun i => neg_le_neg (mul_le_mul_of_nonneg_left (he₁ i) ht.le))
    (fun i => neg_le_neg (mul_le_mul_of_nonneg_left (he₂ i) ht.le)) hm
  rw [hspan,←mul_assoc] at hh
  exact hh

#print axioms gaussian_energy_cover
#print axioms physical_arc_bounds
end
end GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
