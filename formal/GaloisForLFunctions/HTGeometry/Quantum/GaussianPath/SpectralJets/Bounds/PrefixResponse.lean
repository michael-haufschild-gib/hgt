import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.SpectralBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.ModeResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathMicroscopicCircuitOrder

/-! # A deterministic derivative scale for all integer modes on long Gaussian prefixes -/
open Matrix MvPolynomial Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- An upper bound for the response scale, given a coupling box of radius T. -/
def pathResponseCap (N L : ℕ) (T : ℝ) : ℝ :=
  let D : ℕ := 2^N
  let R := pathBoxRadius N T + L + 3
  let K := pencilCap N R
  let M := R*(2+4*(L:ℝ))^L*K^(2*L)
  (1+(D:ℝ)*K^(2*L))*D.factorial*(1+(D:ℝ)*(D*M))^D

private theorem responseScale_le {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (s : Fin D → ℂ)
    {S M : ℝ} (hs : ∀ j, ‖s j‖ ≤ S) (hm : ∀ i j, ‖(A*diagonal s) i j‖ ≤ M) :
    responseScale A s ≤ (1+(D:ℝ)*S)*D.factorial*(1+(D:ℝ)*(D*M))^D := by
  have hsum : ∑ j, ‖s j‖ ≤ D*S := by
    simpa [nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
  have hrows (i : Fin D) : ∑ j, ‖(A*diagonal s) i j‖ ≤ D*M := by
    simpa [nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hm i j)
  have hmat : ∑ i, ∑ j, ‖(A*diagonal s) i j‖ ≤ D*(D*M) := by
    simpa [nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrows i)
  have hDS : 0 ≤ D*S := (Finset.sum_nonneg fun j _ => norm_nonneg (s j)).trans hsum
  unfold responseScale
  gcongr

/-- All nonzero balanced integer combinations of a common analytic root packet
have a response above the stated lower threshold at the same explicit scale. -/
def ModesAtScale (N : ℕ) (rows : Fin (2^N) → Option (List (Coordinates N)))
    (θ : Coordinates N → ℝ) (C a : ℝ) : Prop :=
  let x := fun i => (θ i : ℂ)
  ∃ f : Fin (2^N) → (Coordinates N → ℂ) → ℂ,
    (∀ j, AnalyticAt ℂ (f j) x ∧
      ∀ᶠ z in 𝓝 x, matrixCharpolyRelation (∑ i, z i • chainPauliFin N i,f j z) = 0) ∧
    Function.Injective (fun j => f j x) ∧
    ∀ m : Fin (2^N) → ℤ, m ≠ 0 → ∑ j, m j = 0 →
      ∃ i w, rows i = some w ∧ a ≤ (C*((2^N : ℕ):ℝ)*‖∑ j, mixed w (f j) x*(m j : ℂ)‖)^2

private theorem modes_at_box_scale (N L : ℕ) (rows : Fin (2^N) → Option (List (Coordinates N)))
    (hw : ∀ i w, w ∈ rows i → w.length ≤ L) (θ : Coordinates N → ℝ) {a T : ℝ} (hT : 0 ≤ T)
    (hθ : ∀ i, |θ i| ≤ T) (h : DetectsBalancedModes N L rows θ a) :
    ModesAtScale N rows θ (pathResponseCap N L T) a := by
  let x := fun i => (θ i : ℂ)
  let r := pathBoxRadius N T
  let R := r+L+3
  let K := pencilCap N R
  let p := MvPolynomial.map GaussianInt.toComplex (characteristic (integralGenerators N))
  obtain ⟨f,hf,hi,hrow,hmode⟩ := h
  let A := Matrix.of fun i j => rowValue (rows i) (f j) x
  let s (j) := onRoot (MvPolynomial.pderiv none p) (f j) x^(2*L)
  have hxr (i) : ‖x i‖ ≤ T := by simpa [x,Real.norm_eq_abs] using hθ i
  have hr : 0 ≤ r := hT.trans (pathBoxRadius_ge N hT)
  have hR : 1 ≤ R := by dsimp [R]; linarith only [hr,Nat.cast_nonneg (α := ℝ) L]
  have hmargin : r+(L:ℝ)+2 ≤ R := by dsimp [R]; linarith
  have hb (j) (o : Option (Coordinates N)) : ‖o.elim (f j x) x‖ ≤ r := by
    cases o with
    | none => exact path_root_in_box N x hT hxr (hf j).2.self_of_nhds
    | some i => exact (hxr i).trans (pathBoxRadius_ge N hT)
  have hs (j) : ‖s j‖ ≤ K^(2*L) := by
    have hp : BoxBound p R K := path_characteristic_box_bound N (zero_le_one.trans hR)
    have hd : BoxBound (MvPolynomial.pderiv none p) r K :=
      (hp.shrink (by linarith only [hmargin,Nat.cast_nonneg (α := ℝ) L])).partial none
    rw [show s j = _^(2*L) from rfl,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hd _ (hb j)) _
  have hm (i j) : ‖(A*diagonal s) i j‖ ≤ R*(2+4*(L:ℝ))^L*K^(2*L) := by
    have he : A i j*s j = onRoot (jetRow p L (rows i)) (f j) x := hrow i j
    rw [Matrix.mul_diagonal,he]
    exact path_jetRow_box_bound N L hR hmargin (rows i) (hw i) _ (hb j)
  have hcap : responseScale A s ≤ pathResponseCap N L T := responseScale_le A s hs hm
  have hscale : 0 ≤ responseScale A s := by unfold responseScale; positivity
  refine ⟨f,hf,hi,?_⟩
  intro m hm' hbal
  obtain ⟨i,w,hiw,hresp⟩ := hmode m hm' hbal
  refine ⟨i,w,hiw,hresp.trans ?_⟩
  apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hscale (Nat.cast_nonneg _)) (norm_nonneg _))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg _)) (norm_nonneg _)

private theorem eventually_prefix_box :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      ∀ i, |pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)| ≤ ((k+3:ℕ):ℝ)^2 := by
  obtain ⟨_,b,_,_,hμ⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨m,hm⟩ := exists_nat_gt (12+b)
  filter_upwards [hμ] with ω hω
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω,eventually_ge_atTop m] with k hk hkm
  intro i
  let u := pathPauliDisorderShell ω (k+1)
  have h₁ := Finset.single_le_sum (s := Finset.univ) (f := fun l => |u l|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ (pathCoeffEquiv (k+1) i))
  have h₂ := path_pauli_coefficient_mass_le u b hk.2
  have hn : 12+b ≤ ((k+3:ℕ):ℝ) := hm.le.trans (by exact_mod_cast (show m ≤ k+3 by omega))
  exact h₁.trans (h₂.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg (k+3))))

/-- For one infinite Gaussian Pauli path, every sufficiently long prefix obeys
a common, sample-independent lower derivative threshold for every nonzero
balanced integer mode. The same rows and branches handle all modes. -/
theorem gaussian_path_eventually_uniform_mode_response :
    ∃ rows : (k : ℕ) → Fin (2^(k+3)) → Option (List (Coordinates (k+3))),
      (∀ k i w, w ∈ rows k i → w.length ≤ 2^(k+3)-2) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let B := prefixDetectorDegree k
        let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
        ModesAtScale N (rows k) θ (pathResponseCap N (2^N-2) ((N:ℝ)^2))
          (((1/2:ℝ)^k/(1+2*B))^B) := by
  obtain ⟨rows,hw,hd⟩ := gaussian_path_eventually_detects_balanced_modes
  refine ⟨rows,hw,?_⟩
  filter_upwards [hd,eventually_prefix_box] with ω hω hbox
  filter_upwards [hω,hbox] with k hk hb
  exact modes_at_box_scale _ _ (rows k) (hw k) _ (sq_nonneg _) hb hk

#print axioms gaussian_path_eventually_uniform_mode_response
end
end GaloisForLFunctions.HTGeometry.SpectralJets
