import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EigenstatePreparation.BellBlocks.DimerReplacement
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EigenstatePreparation.BellBlocks.UntouchedBoxes

/-! # Roughly maximally mixed spins untouched by an adaptive set of wires -/
open Filter MeasureTheory Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section
private def target (x : Fin 3 × PathPauliDirections) : ℝ :=
  if x.1.val=1 then
    (if x.2=Sum.inr (0,0) then 1 else 0)+(if x.2=Sum.inr (2,2) then 2 else 0) else 0

private theorem box_error (ω : PathPauliDisorder) (n k : ℕ) (e : Fin (n+1)) (he : e.val=3*k+1)
    {η : ℝ} (hb : ∀ x : Fin 3 × PathPauliDirections, |ω (3*k+x.1.val,x.2)-target x|≤η) :
    ∀ v ∈ ({e.castSucc,e.succ}:Finset (Fin (n+2))), ∀ l, pathIncident v l →
      |pathPauliDisorderShell ω n l-dimerCoeff e l|≤η := by
  intro v hv l hl
  have hv' : v.val=3*k+1 ∨ v.val=3*k+2 := by
    rcases mem_insert.mp hv with h | h
    · exact Or.inl ((congrArg Fin.val h).trans he)
    · have h' := congrArg Fin.val (mem_singleton.mp h)
      change v.val=e.val+1 at h'
      omega
  rcases l with ⟨s,b⟩ | ⟨f,ab⟩
  · change s=v at hl
    subst s
    let r : Fin 3 := ⟨v.val-3*k,by omega⟩
    have hr : 3*k+r.val=v.val := by dsimp only [r]; omega
    have h := hb (r,.inl b)
    change |ω (3*k+r.val,Sum.inl b)-target (r,Sum.inl b)|≤η at h
    rw [hr] at h
    simpa [pathPauliDisorderShell,dimerCoeff,target] using h
  · change f.castSucc=v ∨ f.succ=v at hl
    have hf : f.val=v.val ∨ f.val+1=v.val := hl.imp (congrArg Fin.val) (congrArg Fin.val)
    let r : Fin 3 := ⟨f.val-3*k,by omega⟩
    have hr : 3*k+r.val=f.val := by dsimp only [r]; omega
    have hr1 : r.val=1 ↔ f=e := by
      constructor
      · intro h; exact Fin.ext (by omega)
      · intro h; have := congrArg Fin.val h; omega
    have h := hb (r,.inr ab)
    change |ω (3*k+r.val,Sum.inr ab)-target (r,Sum.inr ab)|≤η at h
    rw [hr] at h
    by_cases hfe : f=e
    · simpa [pathPauliDisorderShell,dimerCoeff,target,hr1,hfe] using h
    · simpa [pathPauliDisorderShell,dimerCoeff,target,hr1,hfe] using h

/-- For any prescribed local replacement accuracy and any sufficiently
sparse set of forbidden wires, a physical dimer misses all those wires.
The three Bloch components on its first site obey the bound simultaneously
in every eigenstate, including the spectral edges. -/
theorem gaussian_untouched_dimer (δ : ℝ) (hδ : 0<δ) :
    ∃ c > (0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Matrix (Fin (n+2) → Bool) _ ℂ) :=
        ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ F : Finset (Fin (n+2)), (F.card:ℝ)<c*(n+2) → ∃ e : Fin (n+1),
        e.castSucc∉F ∧ e.succ∉F ∧ ∀ a i,
          ‖energyDiagonal H (finitePauliMatrix (onsiteWord e.castSucc a)) i‖≤δ := by
  let η := δ/42
  obtain ⟨p,hp,h⟩ := gaussian_untouched_boxes (by decide : 0<3) target η (div_pos hδ (by norm_num))
  refine ⟨p/6,div_pos hp (by norm_num),?_⟩
  filter_upwards [h] with ω hω
  obtain ⟨N,hN⟩ := eventually_atTop.1 hω
  filter_upwards [eventually_ge_atTop (3*N+8)] with n hn
  intro u H F hF
  let m := (n+1)/3
  have hm : N≤m := by dsimp only [m]; omega
  have hsize : (n:ℝ)+2≤6*m := by
    exact_mod_cast (show n+2≤6*m by dsimp only [m]; omega)
  let G := F.image Fin.val
  have hG : (G.card:ℝ)<p*m := by
    have hg : (G.card:ℝ)≤F.card := by exact_mod_cast card_image_le (s:=F) (f:=Fin.val)
    have hvol := mul_le_mul_of_nonneg_left hsize (div_nonneg hp.le (by norm_num : (0:ℝ)≤6))
    linarith only [hg,hF,hvol]
  obtain ⟨k,hk,hout,hbox⟩ := hN m hm G hG
  let e : Fin (n+1) := ⟨3*k+1,by dsimp only [m] at hk; omega⟩
  have hsite (v : Fin (n+2)) (r : Fin 3) (hv : v.val=3*k+r.val) : v∉F := fun hvF =>
    hout r (mem_image.mpr ⟨v,hvF,hv⟩)
  refine ⟨e,hsite e.castSucc 1 rfl,hsite e.succ 2 (by change 3*k+1+1=3*k+2; omega),?_⟩
  intro a i
  have hlocal := dimer_replacement_error u e (div_nonneg hδ.le (by norm_num : (0:ℝ)≤42))
    (box_error ω n k e rfl hbox)
  exact (dimer_bloch_signal u e a i).trans (hlocal.trans_eq (by dsimp only [η]; ring))

#print axioms gaussian_untouched_dimer
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
