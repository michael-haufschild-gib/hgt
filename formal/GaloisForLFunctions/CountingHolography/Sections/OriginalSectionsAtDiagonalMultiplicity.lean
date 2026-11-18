import GaloisForLFunctions.CountingHolography.Sections.TheArchimedeanLimitOnTheSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.TheDiagonalOrdinaryFloorLoss

/-!
# Original sections at diagonal multiplicity

A comparison of two resolutions on each conductor cancels the integrated
prime term. After removal of the actual ordinary floor loss the normalized
surplus at the single multiplicity n recovers the signed Weil degree.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open AbsoluteGeometryOfSpecZ ArithmeticScatteringHolography Filter Topology

private abbrev conductorJet (n r : ℕ) := degreeForm (packet (successorSquareTriple n))
  (3*windowEnd ((2*n+1)^2+1)) r

private abbrev squareSurplus (n m : ℕ) :=
  let a := m • successorSquareTriple n
  radius a-Real.log (generator a : ℝ)

private abbrev signedDegree (n : ℕ) := integerProbe _ (successorSquareTriple n)

private theorem balance_with_sampled_jet : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ m : ℕ,
    let a := m • successorSquareTriple n
    |squareSurplus n m-ordinaryFloorLoss a+
      (m:ℝ)^2*(conductorJet n (resolution a)+fullPrimeContact (successorSquareTriple n))| ≤ C*((n:ℝ)+m) := by
  obtain ⟨C,hC,h⟩ := successorSquare_full_surplus_and_jet
  refine ⟨C,hC,fun {n} hn m => ?_⟩
  have hh := h hn m
  dsimp only at hh ⊢
  rw [jetRadius,packet_smul,degreeForm_mul] at hh
  exact (congrArg abs (by unfold squareSurplus conductorJet; ring)).le.trans hh

/-- At fixed conductor the limiting jet, together with the complete prime
sum, is minus the signed Weil degree. -/
private theorem fixed_conductor_jet {n : ℕ} (hn : 0 < n) :
    Tendsto (fun m : ℕ => conductorJet n (resolution (m • successorSquareTriple n))) atTop
      (𝓝 (-(signedDegree n+fullPrimeContact (successorSquareTriple n)))) := by
  obtain ⟨C,hC,h⟩ := balance_with_sampled_jet
  let d := successorSquareTriple n
  let q := fun m : ℕ => conductorJet n (resolution (m • d))
  let P := fullPrimeContact d
  let L := ((3*windowEnd ((2*n+1)^2+1):ℕ):ℝ)
  let E := C*n+7*L
  have h₁ : Tendsto (fun m : ℕ => E/(m:ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have h₂ : Tendsto (fun m : ℕ => C/(m:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => squareSurplus n m/(m:ℝ)^2+(q m+P)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun m : ℕ => E/(m:ℝ)^2+C/m) _ (by simpa only [add_zero] using h₁.add h₂)
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
    have hh : |squareSurplus n m-ordinaryFloorLoss (m • d)+(m:ℝ)^2*(q m+P)| ≤ C*((n:ℝ)+m) := h hn m
    have hv : 0 ≤ ordinaryFloorLoss (m • d) ∧ ordinaryFloorLoss (m • d) ≤ 7*L := ordinaryFloorLoss_bounds _
    have hs : |squareSurplus n m+(m:ℝ)^2*(q m+P)| ≤ E+C*m := by
      rw [abs_le] at hh ⊢
      dsimp only [E]
      constructor <;> linarith only [hh.1,hh.2,hv.1,hv.2]
    rw [Real.norm_eq_abs,show squareSurplus n m/(m:ℝ)^2+(q m+P)=
      (squareSurplus n m+(m:ℝ)^2*(q m+P))/(m:ℝ)^2 by field_simp,abs_div,abs_of_nonneg (sq_nonneg (m:ℝ))]
    exact (div_le_div_of_nonneg_right hs (sq_nonneg _)).trans_eq (by field_simp)
  have hq : Tendsto (fun m : ℕ => squareSurplus n m/(m:ℝ)^2) atTop (𝓝 (signedDegree n)) := tendsto_splineDegree d
  have ht := (he.sub hq).sub_const P
  rw [show (0:ℝ)-signedDegree n-P= -(signedDegree n+P) by ring] at ht
  exact ht.congr (fun m => by change _=q m; ring)

/-- At every diverging sequence of resolutions, the jet discrepancy from
the exact continuous archimedean term tends to zero along the squares. -/
theorem successorSquare_jet_discrepancy (ν r : ℕ → ℕ) (hν : Tendsto ν atTop atTop) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => degreeForm (packet (successorSquareTriple (ν n))) (3*windowEnd ((2*ν n+1)^2+1)) (r n)+
      (integerProbe _ (successorSquareTriple (ν n))+fullPrimeContact (successorSquareTriple (ν n)))) atTop (𝓝 0) := by
  obtain ⟨z,hz⟩ := successorSquare_archimedean_jet_limit
  let D := fun n => signedDegree n+fullPrimeContact (successorSquareTriple n)
  let b := fun n m : ℕ => conductorJet n (resolution (m • successorSquareTriple n))
  let e := fun n : ℕ => 1/((n:ℝ)+1)
  have pick (n : ℕ) : ∃ m : ℕ, n ≤ m ∧ (0 < n → |b n m+D n| ≤ e n) := by
    by_cases hn : 0 < n
    · have hε : 0 < e n := by dsimp only [e]; positivity
      obtain ⟨m,hm,hnear⟩ := ((eventually_ge_atTop n).and ((Metric.tendsto_nhds.mp (fixed_conductor_jet hn))
        (e n) hε)).exists
      refine ⟨m,hm,fun _ => ?_⟩
      simpa only [Real.dist_eq,sub_neg_eq_add,b,D] using hnear.le
    · exact ⟨n,le_rfl,fun h => (hn h).elim⟩
  choose m hm hsel using pick
  have hres : Tendsto (fun n => resolution (m n • successorSquareTriple n)) atTop atTop :=
    tendsto_atTop_mono (fun n => (hm n).trans (successorSquare_resolution_ge n (m n))) tendsto_id
  have he : Tendsto e atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    (tendsto_atTop_mono (fun n : ℕ => (le_add_of_nonneg_right zero_le_one : (n:ℝ) ≤ n+1)) tendsto_natCast_atTop_atTop)
  have hc : Tendsto (fun n => b n (m n)+D n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := e) _ he
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact hsel n hn
  have hb : Tendsto (fun n => b n (m n)) atTop (𝓝 z) := hz id _ tendsto_id hres
  have hd := (hz ν r hν hr).sub (hb.comp hν)
  rw [sub_self] at hd
  have ht := hd.add (hc.comp hν)
  rw [add_zero] at ht
  exact ht.congr fun n => by change (_-b (ν n) (m (ν n)))+(b (ν n) (m (ν n))+D (ν n))=_; ring

/-- At the exact diagonal multiplicity the full original section surplus,
after subtracting the ordinary floor loss, recovers the signed Weil
degree with error tending to zero at every conductor. -/
theorem diagonal_full_surplus_recovers_signed_degree :
    Tendsto (fun n : ℕ => let a := n • successorSquareTriple n
      (radius a-Real.log (generator a : ℝ)-ordinaryFloorLoss a)/(n:ℝ)^2-
        integerProbe _ (successorSquareTriple n)) atTop (𝓝 0) := by
  obtain ⟨C,_,h⟩ := balance_with_sampled_jet
  let r := fun n => resolution (n • successorSquareTriple n)
  let j := fun n => conductorJet n (r n)
  let P := fun n => fullPrimeContact (successorSquareTriple n)
  let v := fun n => ordinaryFloorLoss (n • successorSquareTriple n)
  have hr : Tendsto r atTop atTop := tendsto_atTop_mono (fun n => successorSquare_resolution_ge n n) tendsto_id
  have he : Tendsto (fun n : ℕ => (squareSurplus n n-v n)/(n:ℝ)^2+(j n+P n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ => (2*C)/(n:ℝ)) _ (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have hh : |squareSurplus n n-v n+(n:ℝ)^2*(j n+P n)| ≤ C*((n:ℝ)+n) := h hn n
    rw [Real.norm_eq_abs,show (squareSurplus n n-v n)/(n:ℝ)^2+(j n+P n)=
      (squareSurplus n n-v n+(n:ℝ)^2*(j n+P n))/(n:ℝ)^2 by field_simp,abs_div,abs_of_nonneg (sq_nonneg (n:ℝ))]
    exact (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq (by field_simp; ring)
  have hj : Tendsto (fun n => j n+(signedDegree n+P n)) atTop (𝓝 0) := successorSquare_jet_discrepancy id r tendsto_id hr
  have ht := he.sub hj
  rw [sub_self] at ht
  exact ht.congr fun n => by
    change ((squareSurplus n n-v n)/(n:ℝ)^2+(j n+P n))-(j n+(signedDegree n+P n))=
      (squareSurplus n n-v n)/(n:ℝ)^2-signedDegree n
    ring

private theorem late_jet_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r ≥ N,
      conductorJet n r+(signedDegree n+fullPrimeContact (successorSquareTriple n)) ≤ ε := by
  by_contra! h
  choose ν hν r hr hh using h
  have ht := successorSquare_jet_discrepancy ν r (tendsto_atTop_mono hν tendsto_id)
    (tendsto_atTop_mono hr tendsto_id)
  obtain ⟨k,hk⟩ := (ht.eventually_lt_const hε).exists
  exact (not_lt_of_ge hk.le) (hh k)

/-- A one-sided bound also covers the finitely many small resolutions. -/
private theorem all_jet_upper : ∃ J : ℝ, 0 ≤ J ∧ ∀ n r : ℕ, 0 < r →
    conductorJet n r+(signedDegree n+fullPrimeContact (successorSquareTriple n)) ≤ J := by
  obtain ⟨z,hz⟩ := successorSquare_archimedean_jet_limit
  let D := fun n => signedDegree n+fullPrimeContact (successorSquareTriple n)
  have h := (successorSquare_jet_discrepancy id id tendsto_id tendsto_id).sub (hz id id tendsto_id tendsto_id)
  have hD : Tendsto D atTop (𝓝 (0-z)) := h.congr fun n => by change (conductorJet n n+D n)-conductorJet n n=D n; ring
  obtain ⟨A,hA⟩ := hD.bddAbove_range
  obtain ⟨B,hB,hjet⟩ := uniform_finite_jet_debit
  refine ⟨16*B+|A|,by positivity,fun n r hr => ?_⟩
  have hd : D n ≤ |A| := (hA ⟨n,rfl⟩).trans (le_abs_self A)
  have hmass := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2
  have hh : conductorJet n r ≤ _ := hjet _ (successorSquareTriple n) _ r hr
  change conductorJet n r+D n ≤ _
  linarith only [hh,mul_le_mul_of_nonneg_left hmass hB,hd]

/-- At every prescribed multiplicity up to any fixed multiple of n, the
original section surplus exceeds the exact signed degree by a fixed
positive multiple of n². The constants are uniform on all late conductors. -/
theorem original_surplus_above_signed_degree_through_linear_scale {K : ℝ} (hK : 1 ≤ K) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m → (m:ℝ) ≤ K*n →
      let a := m • successorSquareTriple n
      Real.log (generator a : ℝ)+(m:ℝ)^2*integerProbe _ (successorSquareTriple n)+γ*(n:ℝ)^2 ≤ radius a := by
  obtain ⟨c,hc,hfloor⟩ := all_multiplicities_through_diagonal_ordinary_floor_loss hK
  obtain ⟨C,hC,hbal⟩ := balance_with_sampled_jet
  obtain ⟨J,hJ,hjet⟩ := all_jet_upper
  have hK' : 0 < K := zero_lt_one.trans_le hK
  let ε := c/(4*K^2)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨N,hN⟩ := late_jet_upper hε
  let D := C*(1+K)+J*(N:ℝ)^2
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hfloor,eventually_ge_atTop N,eventually_ge_atTop 1,eventually_ge_atTop ⌈4*D/c⌉₊]
    with n hf hnN hn₁ hnD
  intro m hm hmK
  let d := successorSquareTriple n
  let a := m • d
  let E := conductorJet n (resolution a)+(signedDegree n+fullPrimeContact d)
  have hm₀ := Nat.cast_nonneg (α := ℝ) m
  have hn₀ := Nat.cast_nonneg (α := ℝ) n
  have hr : m ≤ resolution a := successorSquare_resolution_ge n m
  have hlarge : (m:ℝ)^2*E ≤ ε*(m:ℝ)^2+J*(N:ℝ)^2 := by
    by_cases hNm : N ≤ m
    · have hbound : E ≤ ε := hN n hnN _ (hNm.trans hr)
      linarith only [mul_le_mul_of_nonneg_left hbound (sq_nonneg (m:ℝ)),mul_nonneg hJ (sq_nonneg (N:ℝ))]
    · have hbound : E ≤ J := hjet n _ (hm.trans_le hr)
      have hs : (m:ℝ)^2 ≤ (N:ℝ)^2 := pow_le_pow_left₀ hm₀ (by exact_mod_cast (le_of_lt (lt_of_not_ge hNm))) 2
      linarith only [mul_le_mul_of_nonneg_left hbound (sq_nonneg (m:ℝ)),mul_le_mul_of_nonneg_left hs hJ,
        mul_nonneg hε.le (sq_nonneg (m:ℝ))]
  have hq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm₀ hmK 2) hε.le
  have hid : ε*(K*n)^2 = (c/4)*(n:ℝ)^2 := by dsimp only [ε]; field_simp
  rw [hid] at hq
  have hD : 4*D ≤ (n:ℝ)*c := (div_le_iff₀ hc).mp ((Nat.le_ceil _).trans (by exact_mod_cast hnD))
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  have hconst := le_mul_of_one_le_right (mul_nonneg hJ (sq_nonneg (N:ℝ))) hn'
  have hcost : C*((n:ℝ)+m)+J*(N:ℝ)^2 ≤ (c/4)*(n:ℝ)^2 := by
    dsimp only [D] at hD
    linarith only [mul_le_mul_of_nonneg_right hD hn₀,hconst,mul_le_mul_of_nonneg_left hmK hC]
  have hnR : (n:ℝ) ≤ squareUpperRoot n := by unfold squareUpperRoot; linarith only [hn₀]
  have hv : c*(n:ℝ)^2 ≤ ordinaryFloorLoss a := hf hm (hmK.trans (mul_le_mul_of_nonneg_left hnR hK'.le))
  have hh := (abs_le.mp (hbal hn₁ m)).1
  change -(C*((n:ℝ)+m)) ≤ radius a-Real.log (generator a : ℝ)-ordinaryFloorLoss a+
    (m:ℝ)^2*(conductorJet n (resolution a)+fullPrimeContact d) at hh
  dsimp only [E] at hlarge
  change Real.log (generator a : ℝ)+(m:ℝ)^2*signedDegree n+(c/2)*(n:ℝ)^2 ≤ radius a
  linarith only [hh,hv,hlarge,hq,hcost]

/-- For each fixed K the same arbitrarily late conductors carry exponentially
many original sections at every positive multiplicity through Kn, including
the diagonal. They also carry an eventual tail at the original radius. -/
theorem cofinal_original_sections_through_any_linear_scale {K : ℝ} (hK : 1 ≤ K) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ᶠ n : ℕ in atTop,
      (∀ {m : ℕ}, 0 < m → (m:ℝ) ≤ K*n → let a := m • successorSquareTriple n
        Real.log (generator a : ℝ)+γ*(n:ℝ)^2 ≤ radius a ∧
        2*⌊Real.exp (γ*(n:ℝ)^2)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card) ∧
      (∀ᶠ m : ℕ in atTop, let a := m • successorSquareTriple n
        Real.log (generator a : ℝ) < radius a) := by
  obtain ⟨γ,hγ,hs⟩ := original_surplus_above_signed_degree_through_linear_scale hK
  refine ⟨γ,hγ,(frequently_successorSquare_sections.and_eventually hs).mono ?_⟩
  rintro n ⟨⟨htail,hcount⟩,hn⟩
  refine ⟨fun {m} hm hk => ?_,htail⟩
  let a := m • successorSquareTriple n
  have hQ : 0 ≤ signedDegree n := ge_of_tendsto hcount (Eventually.of_forall fun m =>
    div_nonneg (Nat.cast_nonneg _) (sq_nonneg (m:ℝ)))
  have hb : Real.log (generator a : ℝ)+(m:ℝ)^2*signedDegree n+γ*(n:ℝ)^2 ≤ radius a := hn hm hk
  have hh : Real.log (generator a : ℝ)+γ*(n:ℝ)^2 ≤ radius a := by
    linarith only [hb,mul_nonneg (sq_nonneg (m:ℝ)) hQ]
  refine ⟨hh,?_⟩
  have hpos : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  have he := Real.exp_le_exp.mpr (show γ*(n:ℝ)^2 ≤ radius a-Real.log (generator a : ℝ) by linarith only [hh])
  rw [Real.exp_sub,Real.exp_log hpos] at he
  rw [card_smallSections]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.floor_mono he)) _

/-- At the exact diagonal multiplicity arbitrarily late conductors have
exponentially many sections at their original radius. -/
theorem cofinal_original_sections_at_diagonal_multiplicity :
    ∃ γ : ℝ, 0 < γ ∧ ∃ᶠ n : ℕ in atTop, let a := n • successorSquareTriple n
      Real.log (generator a : ℝ)+γ*(n:ℝ)^2 ≤ radius a ∧
      2*⌊Real.exp (γ*(n:ℝ)^2)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨γ,hγ,h⟩ := cofinal_original_sections_through_any_linear_scale (K := 1) le_rfl
  exact ⟨γ,hγ,(h.and_eventually (eventually_ge_atTop 1)).mono (fun n ⟨hn,hn₁⟩ =>
    hn.1 hn₁ (by rw [one_mul]))⟩

/-- A uniform positive reserve in the signed degree pays every original
multiplicity on the same conductor, including multiplicities above n. -/
theorem all_original_surpluses_of_degree_reserve {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop, δ ≤ integerProbe _ (successorSquareTriple n) →
      ∀ {m : ℕ}, 0 < m → let a := m • successorSquareTriple n
        Real.log (generator a : ℝ)+γ*((n:ℝ)^2+(m:ℝ)^2) ≤ radius a := by
  obtain ⟨c,hc,hsmall⟩ := original_surplus_above_signed_degree_through_linear_scale (K := 1) le_rfl
  obtain ⟨C,hC,hbal⟩ := balance_with_sampled_jet
  have hε : 0 < δ/4 := by linarith only [hδ]
  obtain ⟨N,hN⟩ := late_jet_upper hε
  let γ := min c (δ/4)
  have hγ : 0 < γ := lt_min hc hε
  have hγδ : γ ≤ δ/4 := min_le_right _ _
  have hγc : γ ≤ c := min_le_left _ _
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop N,eventually_ge_atTop 1,eventually_ge_atTop ⌈8*C/δ⌉₊]
    with n hn hnN hn₁ hnC hQ m hm
  let d := successorSquareTriple n
  let a := m • d
  have h₁ := sq_nonneg (m:ℝ)
  have h₂ := sq_nonneg (n:ℝ)
  change Real.log (generator a : ℝ)+γ*((n:ℝ)^2+(m:ℝ)^2) ≤ radius a
  by_cases hmn : m ≤ n
  · have hfit : (m:ℝ) ≤ 1*n := by simpa only [one_mul] using (Nat.cast_le.mpr hmn : (m:ℝ) ≤ n)
    have hh : Real.log (generator a : ℝ)+(m:ℝ)^2*signedDegree n+c*(n:ℝ)^2 ≤ radius a := hn hm hfit
    have hγQ : γ ≤ signedDegree n := by linarith only [hQ,hγδ,hδ]
    linarith only [hh,mul_le_mul_of_nonneg_left hγQ h₁,mul_le_mul_of_nonneg_right hγc h₂]
  · have hnm := le_of_lt (lt_of_not_ge hmn)
    have hnm' : (n:ℝ) ≤ m := by exact_mod_cast hnm
    have h₂' := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) hnm' 2
    have hE := hN n hnN (resolution a) (hnN.trans (hnm.trans (successorSquare_resolution_ge n m)))
    have hC' : 8*C ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp ((Nat.le_ceil _).trans (by exact_mod_cast hnC))
    have hpay : C*((n:ℝ)+m) ≤ (δ/4)*(m:ℝ)^2 := by
      have hCm : 8*C ≤ (m:ℝ)*δ := hC'.trans (mul_le_mul_of_nonneg_right hnm' hδ.le)
      linarith only [mul_le_mul_of_nonneg_right hCm (Nat.cast_nonneg (α := ℝ) m),
        mul_le_mul_of_nonneg_left hnm' hC]
    have hh := (abs_le.mp (hbal hn₁ m)).1
    change -(C*((n:ℝ)+m)) ≤ radius a-Real.log (generator a : ℝ)-ordinaryFloorLoss a+
      (m:ℝ)^2*(conductorJet n (resolution a)+fullPrimeContact d) at hh
    have he : conductorJet n (resolution a)+fullPrimeContact d ≤ -(3*δ/4) := by
      change conductorJet n (resolution a)+(signedDegree n+fullPrimeContact d) ≤ δ/4 at hE
      linarith only [hE,hQ]
    linarith only [hh,(ordinaryFloorLoss_bounds a).1,hpay,mul_le_mul_of_nonneg_left he h₁,
      mul_le_mul_of_nonneg_right hγδ h₁,mul_le_mul_of_nonneg_left h₂' hγ.le]

#print axioms all_original_surpluses_of_degree_reserve
#print axioms successorSquare_jet_discrepancy
#print axioms diagonal_full_surplus_recovers_signed_degree
#print axioms original_surplus_above_signed_degree_through_linear_scale
#print axioms cofinal_original_sections_through_any_linear_scale
#print axioms cofinal_original_sections_at_diagonal_multiplicity

end GaloisForLFunctions.CountingHolography.Sections
