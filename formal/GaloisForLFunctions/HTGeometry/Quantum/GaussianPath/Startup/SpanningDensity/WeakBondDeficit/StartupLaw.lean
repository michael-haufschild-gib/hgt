import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Price

/-! # The gate deficit during the approach to one sweep per bond -/

open Real Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section

/-- For K|t| bounded below and Kt² small, the savings in the actual
minimum gate count compared with a full physical sweep have order
K(K|t|)^(-9/10), uniformly at fixed projective errors in [1/20,1/4].
The ninth power counts weak nine-component bonds. The tenth power in
the cutoff includes the error of discarding each such bond. -/
theorem gaussian_startup_deficit :
    ∃ a>0, ∃ b>0, ∃ c>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let u := pathPauliDisorderShell ω n
      ∀ t : ℝ, a≤K * |t| → K*t^2≤b → ∀ ε∈Icc (1/20:ℝ) (1/4),
        let h := (a/(K * |t|))^(1/10:ℝ)
        ∃ s : ℕ, IsLeast {j | HasProjectiveCircuitApproximation (n+2) ε j
            (unitaryEvolution (pathHamiltonian u) t)} s ∧
          c*K*h^9≤K-1-s ∧ K-1-s≤C*K*h^9 := by
  classical
  obtain ⟨c,hc,C,hC,hbonds⟩ := gaussian_weak_edge_counts
  obtain ⟨_,B,_,hB,hbulk⟩ := gaussian_path_eventual_coefficient_mass
  let a := 1/(720*C)
  let Q := (4:ℝ)*2^20
  let b := min (1/(10000*B)) (a^2/Q)
  have ha : 0<a := by dsimp only [a]; positivity
  have hQ : 0<Q := by dsimp only [Q]; positivity
  have hb : 0<b := lt_min (by positivity) (div_pos (sq_pos_of_pos ha) hQ)
  refine ⟨a,ha,b,hb,c,hc,2*C+9*π/(2*a),by positivity,?_⟩
  filter_upwards [hbonds,hbulk] with ω hw hm
  filter_upwards [hw,hm] with n hn hm
  intro K u t hstart hwindow ε he h
  have hK : 0<K := by dsimp only [K]; positivity
  have hTK := ha.trans_le hstart
  have ht : t≠0 := by intro hz; rw [hz,abs_zero,mul_zero] at hTK; exact hTK.false
  have ht' := abs_pos.mpr ht
  have hh : 0<h := rpow_pos_of_pos (div_pos ha hTK) _
  have h₁ : h≤1 := rpow_le_one (div_nonneg ha.le hTK.le) ((div_le_one hTK).mpr hstart) (by norm_num)
  have h10 : h^10=a/(K * |t|) := by
    change ((a/(K * |t|))^(1/10:ℝ))^10=_
    rw [←rpow_natCast,←rpow_mul (div_nonneg ha.le hTK.le)]
    norm_num
  have hscale : K * |t| * h^10=a := by rw [h10]; field_simp
  have hrad : Q≤K*h^20 := by
    have hu := (le_div_iff₀ hQ).mp (hwindow.trans (min_le_right ..))
    apply le_of_mul_le_mul_right _ (mul_pos hK (sq_pos_of_ne_zero ht))
    calc Q*(K*t^2) ≤ a^2 := by linarith only [hu]
         _ = (K*h^20)*(K*t^2) := by rw [←hscale,mul_pow,mul_pow,sq_abs]; ring
  obtain ⟨hl,hu⟩ := hn h hh h₁ hrad
  have hE : t^2*‖u‖^2≤1/10000 := by
    have hs := (le_div_iff₀ (by positivity : 0<10000*B)).mp (hwindow.trans (min_le_left ..))
    have hh := mul_le_mul_of_nonneg_left hm.2 (sq_nonneg t)
    change t^2*‖u‖^2≤t^2*(B*K) at hh
    linarith only [hs,hh]
  have hshort : |t| * ‖u‖≤1/100 := by
    apply le_of_sq_le_sq _ (by norm_num : (0:ℝ)≤1/100)
    rw [mul_pow,sq_abs]
    linarith only [hE]
  let R := removable u h
  let W := weakEdges u h
  have hRW : R.card≤W.card := Finset.card_le_card (Finset.filter_subset ..)
  have hR : R.card≤n+1 := by simpa only [Fintype.card_fin] using Finset.card_le_univ R
  have hin := affordable_after_pruning u h t
  have hprice : 9 * |t| * h*(R.card:ℝ)≤9*C*a := by
    have hh' := mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr hRW).trans hu)
      (show 0≤9 * |t| * h by positivity)
    apply hh'.trans_eq
    rw [←hscale]
    ring
  have hfit : HasProjectiveCircuitApproximation (n+2) ε ((n+1)-R.card)
      (unitaryEvolution (pathHamiltonian u) t) := by
    obtain ⟨z,hz,D,hD,herr⟩ := hin
    refine ⟨z,hz,D,hD,herr.trans ?_⟩
    have hp : 9*C*a=1/80 := by dsimp only [a]; field_simp; ring
    rw [hp] at hprice
    linarith only [hprice,hE,he.1]
  let A (j : ℕ) := HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution (pathHamiltonian u) t)
  have hex : ∃ j, A j := ⟨_,hfit⟩
  let s := Nat.find hex
  have hleast : IsLeast {j | A j} s := ⟨Nat.find_spec hex,fun _ h => Nat.find_min' hex h⟩
  refine ⟨s,hleast,?_,?_⟩
  · have hs : s+R.card≤n+1 := by have h := hleast.2 hfit; omega
    have hr := (Nat.cast_le (α:=ℝ)).mpr hs
    rw [Nat.cast_add] at hr
    have hK' : K=((n+1:ℕ):ℝ)+1 := by dsimp only [K]; push_cast; ring
    change c*K*h^9≤(R.card:ℝ) at hl
    linarith only [hr,hl,hK']
  · obtain ⟨z,hz,D,hD,herr⟩ := hleast.1
    have hp := deficit_price u s hh ht ⟨z,hz,D,hD,herr.trans he.2⟩ hshort
    have hid : 9*π/(2 * |t| * h)=9*π/(2*a)*(K*h^9) := by
      field_simp
      rw [←hscale]
      ring
    rw [hid] at hp
    have hK' : K=((n+1:ℕ):ℝ)+1 := by dsimp only [K]; push_cast; ring
    linarith only [hp,hu,hK']

#print axioms gaussian_startup_deficit
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
