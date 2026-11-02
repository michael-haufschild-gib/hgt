import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineCosts
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineConeWindowCosts

/-!
# Sparse spline correction on prime-cone windows

Baker separation and a fixed gap from the spline shifts give geometric
interpolation costs on geometric frequency windows, uniformly on a positive
vertical strip. Every correction retains at most three nodes per unit interval.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Prime-cone windows admit exact unit-multiplicity spline correction with
geometric node, span, height, and inverse-residual costs, uniformly on a positive strip. -/
theorem exists_two_prime_sparse_spline_geometric_corrections {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D C₀ : ℝ}
    (hd : 0 < d) (hdD : d < D) (hC₀ : 1 ≤ C₀) :
    ∃ U R : ℝ, 0 < U ∧ 1 < R ∧ ∀ k : ℕ, ∀ δ : ℝ, d ≤ δ → δ ≤ D →
      ∃ n : ℕ, ∃ span H₀ ε : ℝ, 0 < n ∧ 0 < span ∧ 0 < H₀ ∧ 0 < ε ∧
        (n : ℝ) ≤ U*R^k ∧ span ≤ U*R^k ∧ H₀ ≤ U*R^k ∧ 1/ε ≤ U*R^k ∧
        ∀ H : ℝ, H₀ ≤ H →
        ∀ r : (coneSquare (Real.log p) (Real.log q) (quantitativeCutoff C₀ k)) → ℂ,
          (∀ u, ‖r u‖ ≤ ε*n/H^8) →
          ∃ γ : Fin n → ℝ, Function.Injective γ ∧
            (∀ j, γ j ∈ Set.Icc H (H+span)) ∧
            (∀ T : ℝ, ((univ : Finset (Fin n)).filter
              (fun j => γ j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
            ∀ u : (coneSquare (Real.log p) (Real.log q) (quantitativeCutoff C₀ k)),
              (∑ j, (Complex.sinh ((δ : ℂ)+(γ j : ℂ)*Complex.I)/
                ((δ : ℂ)+(γ j : ℂ)*Complex.I))^8*phase u.val (γ j))=r u := by
  classical
  let a := Real.log p
  let b := Real.log q
  have ha : 0 < a := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < b := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨η,hη,hgap⟩ := exists_cone_spline_shift_gap hp hq hpq
  obtain ⟨c,B,hc,hB,hsep⟩ := two_prime_coneSquare_separation hp hq hpq
  obtain ⟨V,W,hV,hW,henv⟩ := exists_spline_cone_window_envelope_growth
    ha hb hd hdD.le hη hc hB.le hC₀
  let E := 1+1/min a b+inverseSplineBound d
  let U := 1+sparseSplineCorrectionCost*(E*V)^20
  let R := 1+W^20
  have hCorr := sparseSplineCorrectionCost_pos
  have hE : 1 ≤ E := by
    have hτ : 0 < min a b := lt_min ha hb
    have hI := (inverseSplineBound_pos hd).le
    have hτ0 : 0 ≤ 1/min a b := by positivity
    dsimp only [E]
    linarith only [hI,hτ0]
  have hWp : 0 < W := lt_trans zero_lt_one hW
  have hR : 1 < R := by
    dsimp only [R]
    linarith only [pow_pos hWp 20]
  refine ⟨U,R,by dsimp only [U]; positivity,hR,?_⟩
  intro k δ hdδ hδD
  let N := quantitativeCutoff C₀ k
  let S := coneSquare a b N
  let t : S → ℝ := fun u => u.val
  let L := (a+b+1)*((N : ℝ)+1)
  let σ := c*(2+4*(N : ℝ))^(-B)
  let X := splineWindowCostEnvelope d D (min a b) η (Fintype.card S) L σ
  have hδ := hd.trans_le hdδ
  have hτ : 0 < min a b := lt_min ha hb
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have ht (u : S) : 0 < t u := coneSquare_positive ha hb u.property
  have htτ (u : S) : min a b ≤ t u := coneSquare_lower ha hb u.property
  have hsymmetric (u : S) : u.val ∈ symmetricSpectrum (coneSquare a b N) :=
    mem_insert_of_mem (mem_union_left _ u.property)
  have hsize (u : S) : |t u| ≤ L := symmetric_coneSquare_radius ha hb N u.val (hsymmetric u)
  have hseparate (u v : S) (huv : u ≠ v) : σ ≤ |t u-t v| :=
    hsep N u.val (hsymmetric u) v.val (hsymmetric v) (fun he => huv (Subtype.ext he))
  have hgap' (u : S) (j : Fin 9) : η ≤ |t u+splineShift j| := by
    obtain ⟨_,m,n,_hm,_hn,he⟩ := (mem_coneSquare_iff a b N u.val).mp u.property
    let u' : PositiveCone a b := ⟨u.val,ht u,⟨(m,n),he⟩⟩
    have hr : (((8 : ℤ)-2*(j.val : ℤ) : ℤ) : ℝ)=splineShift j := by
      simp only [splineShift,Int.cast_sub,Int.cast_ofNat,Int.cast_mul,Int.cast_natCast]
    have hshift : |(((8 : ℤ)-2*(j.val : ℤ) : ℤ) : ℝ)| ≤ 8 := by rw [hr]; exact abs_splineShift_le j
    simpa only [hr] using hgap u' (8-2*(j.val : ℤ)) hshift
  obtain ⟨hX,hδX,hηX,hLX,hAX,hJX,hPX,hQX,hGX,hBX⟩ :=
    finite_spline_data_le_window_envelope hd hdδ hδD hτ hσ hη hL htτ hsize hseparate
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hXV : X ≤ V*W^k := by
    simpa only [X,S,N,L,σ,a,b,Fintype.card_coe] using henv k
  let Y := E*X
  have hXY : X ≤ Y := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hE hX0
  have hY : 1 ≤ Y := hX.trans hXY
  have hmτ : (Fintype.card S:ℝ)*min a b ≤ ∑ u : S, |t u| := by
    calc
      _ = ∑ _u : S, min a b := by simp only [sum_const,card_univ,nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun u _ => (htτ u).trans (le_abs_self _)
  have hmX : (Fintype.card S:ℝ) ≤ X/min a b := (le_div_iff₀ hτ).mpr (hmτ.trans hLX)
  have hEτ : 1/min a b ≤ E := by
    have hI := (inverseSplineBound_pos hd).le
    dsimp only [E]
    linarith only [hI]
  have hmY : (Fintype.card S:ℝ) ≤ Y := hmX.trans (by
    calc
      X/min a b=(1/min a b)*X := by ring
      _ ≤ E*X := mul_le_mul_of_nonneg_right hEτ hX0)
  have hIE : inverseSplineBound d ≤ E := by
    have hτ0 : 0 ≤ 1/min a b := by positivity
    dsimp only [E]
    linarith only [hτ0]
  have hIY : inverseSplineBound δ ≤ Y := (inverseSplineBound_antitone hd hdδ).trans
    (hIE.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hX (zero_le_one.trans hE)))
  obtain ⟨n,span,H₀,ε,hn,hspan,hH₀,hε,hnY,hspanY,hHY,hεY,hrealize⟩ :=
    exists_sparse_spline_correction_polynomial_bound hδ hη hY ht
      (show Function.Injective t from Subtype.val_injective) hgap'
      hmY (hPX.trans hXY) (hQX.trans hXY) hIY (hGX.trans hXY) (hBX.trans hXY)
      (hAX.trans hXY) (hηX.trans hXY) (hδX.trans hXY)
  have hYV : Y ≤ (E*V)*W^k := by
    exact (mul_le_mul_of_nonneg_left hXV (zero_le_one.trans hE)).trans_eq (by ring)
  have hmain : sparseSplineCorrectionCost*Y^20 ≤ U*R^k := by
    calc
      _ ≤ sparseSplineCorrectionCost*((E*V)*W^k)^20 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hY) hYV 20) hCorr.le
      _ = (sparseSplineCorrectionCost*(E*V)^20)*(W^20)^k := by
        rw [mul_pow,← pow_mul,Nat.mul_comm k 20,pow_mul]
        ring
      _ ≤ U*R^k := mul_le_mul (by dsimp only [U]; linarith only [])
        (pow_le_pow_left₀ (pow_nonneg hWp.le 20) (by dsimp only [R]; linarith only []) k)
        (pow_nonneg (pow_nonneg hWp.le 20) k) (by dsimp only [U]; positivity)
  have hcost (j : ℕ) (hj : j ≤ 20) : sparseSplineCorrectionCost*Y^j ≤ U*R^k :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY hj) hCorr.le).trans hmain
  exact ⟨n,span,H₀,ε,hn,hspan,hH₀,hε,hnY.trans (hcost 16 (by omega)),
    hspanY.trans (hcost 16 (by omega)),hHY.trans hmain,hεY.trans (hcost 3 (by omega)),hrealize⟩

#print axioms exists_two_prime_sparse_spline_geometric_corrections
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
