import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.LocalSublevel
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.WindingForecast
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-! # Determinant control at a true entry on a growing field interval -/

open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
open PrecisionReturns SharpOccupation
noncomputable section

/-- A single small gap costs one extra factor of the field scale in a
determinant bound. Absorb it into the Dth power before taking a sublevel length. -/
private theorem absorb_scale {D : ℕ} (hD : 0<D) {c Q M S r : ℝ}
    (hc : 0<c) (hQ : 0≤Q) (hM : 0≤M) (hS : 1≤S) (hr : 0≤r) :
    Q*S*r^D*(M*S)^D ≤ c/2*((max 1 (2*Q/c)*M)*S^2*r)^D := by
  let a := max 1 (2*Q/c)
  have ha : 1≤a := le_max_left .. 
  have hQ' : Q≤c/2*a := by
    have h := (div_le_iff₀ hc).mp (le_max_right 1 (2*Q/c))
    linarith only [h]
  have hpow {u : ℝ} (hu : 1≤u) : u≤u^D := by
    simpa only [pow_one] using pow_le_pow_right₀ hu hD
  have hs : Q*S≤c/2*(a*S)^D := calc
    Q*S ≤ (c/2*a)*S := mul_le_mul_of_nonneg_right hQ' (zero_le_one.trans hS)
    _ = c/2*(a*S) := mul_assoc .. 
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpow (ha.trans (le_mul_of_one_le_right (zero_le_one.trans ha) hS))) (half_pos hc).le
  have h := mul_le_mul_of_nonneg_right hs (mul_nonneg (pow_nonneg hr D)
    (pow_nonneg (mul_nonneg hM (zero_le_one.trans hS)) D))
  calc
    _ = Q*S*(r^D*(M*S)^D) := mul_assoc .. 
    _ ≤ _ := h
    _ = _ := by simp only [mul_pow,pow_two]; ring

/-- On |y|≤S every entry within r^D of T belongs to one of O(S)
winding sublevels with Remez parameter O(S²r), uniformly in the exterior
origin. Here D is the square of the Hilbert dimension. -/
theorem shell_entry_sublevel {N : ℕ} (A Z : Register N)
    (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian) {T ε c : ℝ}
    (hT : 0<T) (he : ε∈Ioo (0:ℝ) (sqrt 2)) (hc : 0<c) :
    let D := Fintype.card (Fin N → Bool)^2
    let x := physicalArc ε
    let b (n : ℤ) := 2*π*((n:ℝ)+x)/T
    let H (y : ℝ) : selfAdjoint (Register N) := ⟨A+(y:ℂ) • Z,(hH y).isSelfAdjoint⟩
    ∃ L> (0:ℝ), ∃ C> (0:ℝ), ∀ S≥(1:ℝ), ∀ r∈Ioc (0:ℝ) 1, ∀ y : ℝ, |y|≤S →
      ∀ a> (0:ℝ), ε<orbitCircuitDistance (H y) 0 a →
      |firstVisit (H y) a 0 ε-T|<r^D → ∃ n∈windingBox T (L*S),
        ‖(gapPencil A Z (b n)).det.eval (y:ℂ)‖≤c/2*(C*S^2*r)^D := by
  intro D x b H
  let L := 2*(1+‖A‖+‖Z‖)
  let Q := L/T
  let M := 1+2*L+Q
  have hL : 0<L := by dsimp only [L]; linarith only [norm_nonneg A,norm_nonneg Z]
  have hQ : 0<Q := div_pos hL hT
  have hM : 0<M := by dsimp only [M]; linarith only [hL,hQ]
  have hD : 0<D := pow_pos Fintype.card_pos _
  have hx := (physicalArc_spec he.1 he.2).1
  refine ⟨L,hL,max 1 (2*Q/c)*M,mul_pos (lt_max_of_lt_left zero_lt_one) hM,?_⟩
  intro S hS r hr y hy a ha hout ht
  have hS₀ := zero_le_one.trans hS
  let E := (hH y).eigenvalues
  have hE (i) : |E i|≤L*S/2 := by
    have hh := norm_add_le A ((y:ℂ) • Z)
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at hh
    have haS := mul_le_mul_of_nonneg_left hS (norm_nonneg A)
    have hzS := mul_le_mul_of_nonneg_right hy (norm_nonneg Z)
    apply (abs_eigenvalue_le_l2_opNorm (hH y) i).trans
    dsimp only [L]
    linarith only [hh,haS,hzS,hS₀]
  let v := firstVisit (H y) a 0 ε
  obtain ⟨hv,i,j,n,_,hn⟩ := first_entry_gap (H y) ha he.1 he.2 hout
  let g := E i-E j
  have hg : |g|≤L*S := (abs_sub _ _).trans (by linarith only [hE i,hE j])
  have hwin : |v-T|≤1 := ht.le.trans (pow_le_one₀ hr.1.le hr.2)
  obtain ⟨hbox,hnear⟩ := winding_forecast hT (mul_nonneg hL.le hS₀)
    ⟨hx.1.le,hx.2.le.trans (by norm_num)⟩ v g n hv hwin hg hn
  have hs : L*S/T=Q*S := by dsimp only [Q]; ring
  change |b n-g|≤L*S/T*|v-T| at hnear
  rw [hs] at hnear
  have hQS := mul_nonneg hQ.le hS₀
  have hgap := hnear.trans (mul_le_mul_of_nonneg_left ht.le hQS)
  have hbn : |b n|≤(Q+L)*S := by
    have htri := abs_add_le (b n-g) g
    rw [sub_add_cancel] at htri
    have h := hnear.trans (mul_le_mul_of_nonneg_left hwin hQS)
    linarith only [htri,h,hg]
  have hfac : 1+|b n|+2*max (L*S/2) 0≤M*S := by
    rw [max_eq_left (half_nonneg (mul_nonneg hL.le hS₀))]
    dsimp only [M]
    linarith only [hS,hbn]
  refine ⟨n,hbox,?_⟩
  rw [eval_gapPencil]
  refine (gap_determinant_bound _ (hH y) _ _ hE i j).trans ?_
  refine (mul_le_mul hgap (pow_le_pow_left₀ (by positivity) hfac D) (by positivity)
    (mul_nonneg hQS (pow_nonneg hr.1.le D))).trans ?_
  exact absorb_scale hD hc hQ.le hM.le hS hr.1.le

#print axioms shell_entry_sublevel
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
