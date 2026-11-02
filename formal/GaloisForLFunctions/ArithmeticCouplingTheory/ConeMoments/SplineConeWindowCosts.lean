import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineWindowBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineQuantitativeCorrection
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.QuantitativeConeCutoffs

/-!
# Exact spline correction costs on prime cones

Baker separation and the fixed spline-shift gap make every finite correction
cost grow geometrically along geometric square windows, uniformly on a
positive vertical strip. Coefficients remain prescribed and multiplicities one.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma coneSquare_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {N : ℕ} {u : ℝ}
    (hu : u ∈ coneSquare a b N) : min a b ≤ u := by
  obtain ⟨hu0,m,n,_hm,_hn,rfl⟩ := (mem_coneSquare_iff a b N u).mp hu
  by_cases hm : m=0
  · have hn : n ≠ 0 := by
      intro hn
      apply hu0
      simp only [coneFrequency,hm,hn,Nat.cast_zero,zero_mul,zero_add]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    dsimp only [coneFrequency]
    rw [hm,Nat.cast_zero,zero_mul,zero_add]
    exact (min_le_right a b).trans (by nlinarith only [mul_le_mul_of_nonneg_right hnR hb.le])
  · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    dsimp only [coneFrequency]
    calc
      min a b ≤ a := min_le_left _ _
      _ ≤ (m : ℝ)*a := by nlinarith only [mul_le_mul_of_nonneg_right hmR ha.le]
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hb.le)

/-- Along geometric cone cutoffs, the reciprocal Baker separation grows geometrically. -/
lemma inverse_cone_separation_geometric_bound {c B C : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) (hC : 1 ≤ C) (k : ℕ) :
    1/(c*(2+4*(quantitativeCutoff C k : ℝ))^(-B)) ≤
      ((4*(C+2))^B/c)*((8 : ℝ)^B)^k := by
  let N := quantitativeCutoff C k
  have hbase : 0 < 2+4*(N : ℝ) := by positivity
  have hQ : 0 < C+2 := by linarith only [hC]
  have hN := quantitativeCutoff_upper (le_trans zero_le_one hC) k
  have hN' : 2+4*(N : ℝ) ≤ (4*(C+2))*(8 : ℝ)^k := by
    dsimp only [N]
    nlinarith only [hN]
  calc
    _ = (2+4*(N : ℝ))^B/c := by
      rw [Real.rpow_neg hbase.le]
      field_simp [hc.ne',(Real.rpow_pos_of_pos hbase B).ne']
    _ ≤ ((4*(C+2))*(8 : ℝ)^k)^B/c :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow hbase.le hN' hB) hc.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 4*(C+2)) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) k),
        rpow_nat_power 8 (by norm_num) k B]
      ring

#print axioms coneSquare_lower
#print axioms inverse_cone_separation_geometric_bound
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma spline_window_product_geometric_bound {m L σ M R : ℝ} (hm : 0 ≤ m)
    (hL : 0 ≤ L) (hσ : 0 < σ) (hM : 1 ≤ M) (hR : 1 ≤ R) (k : ℕ)
    (hmM : m+1 ≤ M*R^k) (hLM : L+9 ≤ M*R^k) (hσM : 1/σ ≤ M*R^k) :
    (m+1)^2*((L+9)^2+1/σ) ≤ 2*M^4*(R^4)^k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  let Y := M*R^k
  have hY : 1 ≤ Y := by
    simpa only [one_mul] using mul_le_mul hM (one_le_pow₀ hR)
      (by norm_num : (0 : ℝ) ≤ 1) hM0
  have hY0 : 0 ≤ Y := le_trans zero_le_one hY
  have hY2 : Y ≤ Y^2 := by
    have hh := mul_le_mul_of_nonneg_left hY hY0
    nlinarith only [hh]
  have hm2 : (m+1)^2 ≤ Y^2 := pow_le_pow_left₀ (by positivity) hmM 2
  have hL2 : (L+9)^2 ≤ Y^2 := pow_le_pow_left₀ (by positivity) hLM 2
  have hsum : (L+9)^2+1/σ ≤ 2*Y^2 := by linarith only [hL2,hσM,hY2]
  calc
    _ ≤ Y^2*(2*Y^2) := mul_le_mul hm2 hsum (by positivity) (sq_nonneg Y)
    _ = 2*M^4*(R^4)^k := by
      have he : (R^k)^4=(R^4)^k := by
        rw [← pow_mul, Nat.mul_comm k 4, pow_mul]
      calc
        Y^2*(2*Y^2)=2*(M*R^k)^4 := by dsimp only [Y]; ring
        _ = 2*M^4*(R^k)^4 := by rw [mul_pow]; ring
        _ = _ := by rw [he]


#print axioms spline_window_product_geometric_bound
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The explicit scalar envelope grows geometrically along square cone cutoffs. -/
theorem exists_spline_cone_window_envelope_growth {a b d D η c B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d ≤ D) (hη : 0 < η)
    (hc : 0 < c) (hB : 0 ≤ B) (hC : 1 ≤ C) :
    ∃ U R : ℝ, 0 < U ∧ 1 < R ∧ ∀ k : ℕ,
      splineWindowCostEnvelope d D (min a b) η
        ((coneSquare a b (quantitativeCutoff C k)).card : ℝ)
        ((a+b+1)*((quantitativeCutoff C k : ℝ)+1))
        (c*(2+4*(quantitativeCutoff C k : ℝ))^(-B)) ≤ U*R^k := by
  let Q := C+2
  let V := splineStripCostConstant d D (min a b) η
  let M₀ := 2*Q^2
  let L₀ := (a+b+10)*Q
  let T₀ := (4*Q)^B/c
  let M := 1+M₀+L₀+T₀
  let R := 1+64+8+(8 : ℝ)^B
  have hQ : 0 < Q := by dsimp only [Q]; linarith only [hC]
  have hM₀ : 0 ≤ M₀ := by dsimp only [M₀]; positivity
  have hL₀ : 0 ≤ L₀ := by dsimp only [L₀]; positivity
  have hT₀ : 0 ≤ T₀ := by dsimp only [T₀]; positivity
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hM₀,hL₀,hT₀]
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM₀M : M₀ ≤ M := by dsimp only [M]; linarith only [hL₀,hT₀]
  have hL₀M : L₀ ≤ M := by dsimp only [M]; linarith only [hM₀,hT₀]
  have hT₀M : T₀ ≤ M := by dsimp only [M]; linarith only [hM₀,hL₀]
  have h8B : 0 < (8 : ℝ)^B := Real.rpow_pos_of_pos (by norm_num) B
  have hR : 1 < R := by dsimp only [R]; linarith only [h8B]
  have h64R : (64 : ℝ) ≤ R := by dsimp only [R]; linarith only [h8B]
  have h8R : (8 : ℝ) ≤ R := by dsimp only [R]; linarith only [h8B]
  have h8BR : (8 : ℝ)^B ≤ R := by dsimp only [R]; linarith only []
  have hτ : 0 < min a b := lt_min ha hb
  have hD : 0 ≤ D := (hd.trans_le hdD).le
  have hNum := splineNumeratorEnvelope_nonneg D
  have hInv := (inverseSplineBound_pos hd).le
  have hV : 0 < V := by dsimp only [V,splineStripCostConstant]; positivity
  have hR4 : 1 < R^4 := hR.trans_le (by
    simpa only [pow_one] using pow_le_pow_right₀ hR.le (by omega : 1 ≤ 4))
  refine ⟨2*V*M^4,R^4,by positivity,hR4,?_⟩
  intro k
  let N := quantitativeCutoff C k
  let m : ℝ := (coneSquare a b N).card
  let L := (a+b+1)*((N : ℝ)+1)
  let σ := c*(2+4*(N : ℝ))^(-B)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hN := quantitativeCutoff_upper (le_trans zero_le_one hC) k
  change (N : ℝ)+1 ≤ Q*(8 : ℝ)^k at hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hmCard : m ≤ ((N : ℝ)+1)^2 := by
    dsimp only [m]
    exact_mod_cast coneSquare_card_le a b N
  have hmRate : m+1 ≤ M₀*(64 : ℝ)^k := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ (N : ℝ)+1 by positivity) hN 2
    have h8pow : ((8 : ℝ)^k)^2=(64 : ℝ)^k := by
      rw [← pow_mul,Nat.mul_comm k 2,pow_mul]
      norm_num
    rw [mul_pow,h8pow] at hpow
    have hOne : 1 ≤ ((N : ℝ)+1)^2 := by nlinarith only [hN0,sq_nonneg (N : ℝ)]
    dsimp only [M₀]
    nlinarith only [hmCard,hpow,hOne]
  have hmM : m+1 ≤ M*R^k := hmRate.trans (mul_le_mul hM₀M
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) h64R k)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 64) k) hM0)
  have hLRate : L+9 ≤ L₀*(8 : ℝ)^k := by
    calc
      _ ≤ (a+b+10)*((N : ℝ)+1) := by dsimp only [L]; nlinarith only [hN0]
      _ ≤ (a+b+10)*(Q*(8 : ℝ)^k) := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by dsimp only [L₀]; ring
  have hLM : L+9 ≤ M*R^k := hLRate.trans (mul_le_mul hL₀M
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) h8R k)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) k) hM0)
  have hσRate : 1/σ ≤ T₀*((8 : ℝ)^B)^k := inverse_cone_separation_geometric_bound hc hB hC k
  have hσM : 1/σ ≤ M*R^k := hσRate.trans (mul_le_mul hT₀M
    (pow_le_pow_left₀ h8B.le h8BR k) (pow_nonneg h8B.le k) hM0)
  have hp := spline_window_product_geometric_bound hm0 hL hσ hM hR.le k hmM hLM hσM
  change V*((m+1)^2)*((L+9)^2+1/σ) ≤ _
  calc
    V*((m+1)^2)*((L+9)^2+1/σ)=V*((m+1)^2*((L+9)^2+1/σ)) := by ring
    _ ≤ V*(2*M^4*(R^4)^k) := mul_le_mul_of_nonneg_left hp hV.le
    _ = _ := by ring

#print axioms exists_spline_cone_window_envelope_growth
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Prime-cone windows admit exact unit-multiplicity spline correction with
geometric node, span, height, and inverse-residual costs, uniformly on a positive strip. -/
theorem exists_two_prime_spline_geometric_corrections {p q : ℕ}
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
  let U := 1+splineCorrectionCostConstant*V^9
  let R := 1+W^9
  have hCorr := splineCorrectionCostConstant_pos
  have hWp : 0 < W := lt_trans zero_lt_one hW
  have hR : 1 < R := by
    dsimp only [R]
    linarith only [pow_pos hWp 9]
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
  obtain ⟨n,span,H₀,ε,hn,hspan,hH₀,hε,hnX,hspanX,hHX,hεX,hrealize⟩ :=
    exists_prescribed_spline_correction_polynomial_bound hδ hη hX ht
      (show Function.Injective t from Subtype.val_injective) hgap'
      hδX hηX hLX hAX hJX hPX hQX hGX hBX
  have hmain : splineCorrectionCostConstant*X^9 ≤ U*R^k := by
    calc
      _ ≤ splineCorrectionCostConstant*(V*W^k)^9 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hXV 9) hCorr.le
      _ = (splineCorrectionCostConstant*V^9)*(W^9)^k := by
        rw [mul_pow,← pow_mul,Nat.mul_comm k 9,pow_mul]
        ring
      _ ≤ U*R^k := mul_le_mul (by dsimp only [U]; linarith only [])
        (pow_le_pow_left₀ (pow_nonneg hWp.le 9) (by dsimp only [R]; linarith only []) k)
        (pow_nonneg (pow_nonneg hWp.le 9) k) (by dsimp only [U]; positivity)
  have hcost (j : ℕ) (hj : j ≤ 9) : splineCorrectionCostConstant*X^j ≤ U*R^k :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hj) hCorr.le).trans hmain
  exact ⟨n,span,H₀,ε,hn,hspan,hH₀,hε,hnX.trans (hcost 6 (by omega)),
    hspanX.trans (hcost 5 (by omega)),hHX.trans hmain,hεX.trans (hcost 3 (by omega)),hrealize⟩

#print axioms exists_two_prime_spline_geometric_corrections
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
