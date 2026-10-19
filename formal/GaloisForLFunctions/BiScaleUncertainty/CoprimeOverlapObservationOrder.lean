import GaloisForLFunctions.BiScaleUncertainty.CoprimeOverlapSieveFamily
import GaloisForLFunctions.BiScaleUncertainty.CoprimeOverlapQuarticReadout
import GaloisForLFunctions.BiScaleUncertainty.IncomparableSieveQuartic

/-!
# Sharp translated-observation degree of overlapping sieve modes

For the orders `2pq,2pr,2qr`, affine data and fourth translated moments recover
one common sign when all three coordinates are active. Any missing coordinate
restores independent signs through degree five; sixth moments recover the
common sign. The final threshold compares arbitrary competing sieve weights
and identifies the ambiguity with actual integer translation.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CoprimeOverlap.Triangle
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

def CommonSign (a b : Fin 3 → ℝ) : Prop :=
  (∀ i, a i = b i) ∨ (∀ i, a i = -b i)

def AtMostOne (a : Fin 3 → ℝ) : Prop :=
  ∀ i j, i ≠ j → a i = 0 ∨ a j = 0

def Full (a : Fin 3 → ℝ) : Prop := ∀ i, a i ≠ 0

/-- All labelled affine data together with all translated degrees through m. -/
def ObservationsThrough (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ) (m : ℕ) : Prop :=
  (∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t =
    affineMoment (D.cutoff n) (D.weights n b) s t) ∧
  ∀ k ≤ m, ∀ h : Fin k → ℕ,
    translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) (D.weights n b) h

private theorem squares_of_common {a b : Fin 3 → ℝ} (h : CommonSign a b) :
    ∀ i, (a i)^2 = (b i)^2 := by
  rcases h with h | h <;> intro i <;> rw [h i]
  ring

theorem observations_of_common (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ)
    (hc : CommonSign a b) (m : ℕ) : D.ObservationsThrough n a b m := by
  refine ⟨(D.affine_iff_squares n a b).mpr (squares_of_common hc),?_⟩
  intro k _ h
  rcases hc with he | he
  · rw [funext he]
  · rw [funext he,D.moment_neg]

private theorem common_of_products (a b : Fin 3 → ℝ)
    (he : ∀ i j, a i*a j = b i*b j) : CommonSign a b := by
  rcases (pair_products_eq_iff_common_sign Set.univ a b).mp
    (fun i _ j _ => he i j) with h | h
  · exact Or.inl (fun i => h i (Set.mem_univ i))
  · exact Or.inr (fun i => h i (Set.mem_univ i))

private theorem zero_of_square {x y : ℝ} (he : x^2 = y^2) (hx : x = 0) : y = 0 := by
  apply mul_self_eq_zero.mp
  simpa only [hx,pow_two,zero_mul] using he.symm

/-- A support of size at most one needs no translated observations. -/
theorem common_of_atMostOne (a b : Fin 3 → ℝ) (ha : AtMostOne a)
    (hsq : ∀ i, (a i)^2 = (b i)^2) : CommonSign a b := by
  apply common_of_products
  intro i j
  by_cases hij : i = j
  · subst j
    simpa only [pow_two] using hsq i
  · rcases ha i j hij with hi | hj
    · rw [hi,zero_of_square (hsq i) hi,zero_mul,zero_mul]
    · rw [hj,zero_of_square (hsq j) hj,mul_zero,mul_zero]

/-- Existing sixth-order block recovery applies to the realized overlapping modes. -/
theorem sixth_iff_common (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ) :
    (∀ h : Fin 6 → ℕ,
      translatedMoment (D.cutoff n) (D.weights n a) h =
        translatedMoment (D.cutoff n) (D.weights n b) h) ↔ CommonSign a b := by
  constructor
  · intro h
    rcases sixth_moments_recover_valuation_block (D.cutoff n) 1
      (D.weights n a) (D.weights n b) h with he | he
    · left
      intro i
      have hm : 2^1*D.oddPart i ∈ Finset.Icc 1 (D.cutoff n) := by
        rw [← D.order_eq_oddPart]
        exact D.order_mem n i
      have hh := he (D.oddPart i) (D.oddPart_odd i) hm
      simpa only [← D.order_eq_oddPart,D.coordinate_weights_order] using hh
    · right
      intro i
      have hm : 2^1*D.oddPart i ∈ Finset.Icc 1 (D.cutoff n) := by
        rw [← D.order_eq_oddPart]
        exact D.order_mem n i
      have hh := he (D.oddPart i) (D.oddPart_odd i) hm
      simpa only [← D.order_eq_oddPart,D.coordinate_weights_order] using hh
  · intro h
    exact (D.observations_of_common n a b h 6).2 6 (le_refl 6)

/-- Every coefficient sign is invisible through degree three. -/
theorem through_three_of_squares (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) : D.ObservationsThrough n a b 3 := by
  refine ⟨(D.affine_iff_squares n a b).mpr hsq,?_⟩
  intro m hm h
  interval_cases m
  · simp [translatedMoment]
  · rw [D.odd_moment_zero n a 0 h,D.odd_moment_zero n b 0 h]
  · exact quadratic_moments_of_coordinate_squares _ _ _ (D.coordinate_squares n a b hsq) h
  · rw [D.odd_moment_zero n a 1 h,D.odd_moment_zero n b 1 h]

/-- Removing any coordinate restores independent-sign ambiguity of all quartic lags. -/
theorem quartic_of_missing_mode (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) (hz : ∃ i, a i = 0) (h : Fin 4 → ℕ) :
    translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) (D.weights n b) h := by
  obtain ⟨i,hi⟩ := hz
  have hb := zero_of_square (hsq i) hi
  fin_cases i
  · change a 0 = 0 at hi
    change b 0 = 0 at hb
    apply incomparable_quartic_moments _ (D.order 1) (D.order 2) _ _
      (D.order_not_dvd 1 2 (by decide)) (D.order_not_dvd 2 1 (by decide)) _ _
      (D.coordinate_squares n a b hsq _) (D.coordinate_squares n a b hsq _) h
    · intro q h1 h2
      simp only [D.coordinate_weights,profile,Fin.sum_univ_three,hi,
        if_neg (Ne.symm h1),if_neg (Ne.symm h2)]
      split_ifs <;> simp
    · intro q h1 h2
      simp only [D.coordinate_weights,profile,Fin.sum_univ_three,hb,
        if_neg (Ne.symm h1),if_neg (Ne.symm h2)]
      split_ifs <;> simp
  · change a 1 = 0 at hi
    change b 1 = 0 at hb
    apply incomparable_quartic_moments _ (D.order 0) (D.order 2) _ _
      (D.order_not_dvd 0 2 (by decide)) (D.order_not_dvd 2 0 (by decide)) _ _
      (D.coordinate_squares n a b hsq _) (D.coordinate_squares n a b hsq _) h
    · intro q h0 h2
      simp only [D.coordinate_weights,profile,Fin.sum_univ_three,hi,
        if_neg (Ne.symm h0),if_neg (Ne.symm h2)]
      split_ifs <;> simp
    · intro q h0 h2
      simp only [D.coordinate_weights,profile,Fin.sum_univ_three,hb,
        if_neg (Ne.symm h0),if_neg (Ne.symm h2)]
      split_ifs <;> simp
  · change a 2 = 0 at hi
    change b 2 = 0 at hb
    apply incomparable_quartic_moments _ (D.order 0) (D.order 1) _ _
      (D.order_not_dvd 0 1 (by decide)) (D.order_not_dvd 1 0 (by decide)) _ _
      (D.coordinate_squares n a b hsq _) (D.coordinate_squares n a b hsq _) h
    · intro q h0 h1
      simp only [D.coordinate_weights,profile,Fin.sum_univ_three,hi,
        if_neg (Ne.symm h0),if_neg (Ne.symm h1)]
      split_ifs <;> simp
    · intro q h0 h1
      simp only [D.coordinate_weights,profile,Fin.sum_univ_three,hb,
        if_neg (Ne.symm h0),if_neg (Ne.symm h1)]
      split_ifs <;> simp

/-- Every missing-mode stratum retains all independent signs through degree five. -/
theorem through_five_of_missing_mode (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) (hz : ∃ i, a i = 0) :
    D.ObservationsThrough n a b 5 := by
  refine ⟨(D.affine_iff_squares n a b).mpr hsq,?_⟩
  intro m hm h
  by_cases h3 : m ≤ 3
  · exact (D.through_three_of_squares n a b hsq).2 m h3 h
  · have hm' : m = 4 ∨ m = 5 := by omega
    rcases hm' with rfl | rfl
    · exact D.quartic_of_missing_mode n a b hsq hz h
    · rw [D.odd_moment_zero n a 2 h,D.odd_moment_zero n b 2 h]

/-- One quartic Fourier readout for each possible bridging coordinate. -/
def readouts (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![fourthReadout (D.cutoff n) D.r D.p D.q (D.weights n a),
    fourthReadout (D.cutoff n) D.q D.p D.r (D.weights n a),
    fourthReadout (D.cutoff n) D.p D.q D.r (D.weights n a)]

theorem readouts_eq (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (i : Fin 3) :
    D.readouts n a i = ((D.cutoff n).factorial : ℝ)^4 *
      ![a 1*a 2*(a 0)^2,a 0*a 2*(a 1)^2,a 0*a 1*(a 2)^2] i := by
  obtain ⟨hN,hpN,hqN,hrN⟩ := D.base_mem n
  have h0 : selbergMultiplesCoord (D.cutoff n) (D.weights n a) (2*D.p*D.q) = a 0 :=
    D.coordinate_weights_order n a 0
  have h1 : selbergMultiplesCoord (D.cutoff n) (D.weights n a) (2*D.p*D.r) = a 1 :=
    D.coordinate_weights_order n a 1
  have h2 : selbergMultiplesCoord (D.cutoff n) (D.weights n a) (2*D.q*D.r) = a 2 :=
    D.coordinate_weights_order n a 2
  have hrp : 2*D.r*D.p = 2*D.p*D.r := by ring
  have hrq : 2*D.r*D.q = 2*D.q*D.r := by ring
  have hqp : 2*D.q*D.p = 2*D.p*D.q := by ring
  fin_cases i
  · change fourthReadout (D.cutoff n) D.r D.p D.q (D.weights n a) =
      ((D.cutoff n).factorial : ℝ)^4 * (a 1*a 2*(a 0)^2)
    have hh := fourthReadout_eq hN D.hr D.hp D.hq hrN hpN hqN
      D.hpr.symm D.hqr.symm D.hpq (D.weights n a)
    rw [hrp,hrq,h0,h1,h2] at hh
    simpa only [mul_assoc] using hh
  · change fourthReadout (D.cutoff n) D.q D.p D.r (D.weights n a) =
      ((D.cutoff n).factorial : ℝ)^4 * (a 0*a 2*(a 1)^2)
    have hh := fourthReadout_eq hN D.hq D.hp D.hr hqN hpN hrN
      D.hpq.symm D.hqr D.hpr (D.weights n a)
    rw [hqp,h0,h1,h2] at hh
    simpa only [mul_assoc] using hh
  · change fourthReadout (D.cutoff n) D.p D.q D.r (D.weights n a) =
      ((D.cutoff n).factorial : ℝ)^4 * (a 0*a 1*(a 2)^2)
    have hh := fourthReadout_eq hN D.hp D.hq D.hr hpN hqN hrN
      D.hpq D.hpr D.hqr (D.weights n a)
    rw [h0,h1,h2] at hh
    simpa only [mul_assoc] using hh

/-- Active overlap converts quartic data and magnitudes into one common sign. -/
theorem common_of_full_quartic (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ)
    (hfull : Full a) (hsq : ∀ i, (a i)^2 = (b i)^2)
    (hm : ∀ h : Fin 4 → ℕ,
      translatedMoment (D.cutoff n) (D.weights n a) h =
        translatedMoment (D.cutoff n) (D.weights n b) h) : CommonSign a b := by
  have hr (p q r : ℕ) : fourthReadout (D.cutoff n) p q r (D.weights n a) =
      fourthReadout (D.cutoff n) p q r (D.weights n b) := by
    unfold fourthReadout
    simp_rw [hm]
  have he (i : Fin 3) : D.readouts n a i = D.readouts n b i := by
    fin_cases i <;> apply hr
  have hP : (((D.cutoff n).factorial : ℝ)^4) ≠ 0 := by positivity
  have h01 : a 0*a 1 = b 0*b 1 := by
    have hh := he 2
    rw [D.readouts_eq,D.readouts_eq] at hh
    change ((D.cutoff n).factorial : ℝ)^4 * (a 0*a 1*(a 2)^2) =
      ((D.cutoff n).factorial : ℝ)^4 * (b 0*b 1*(b 2)^2) at hh
    have ht := mul_left_cancel₀ hP hh
    rw [← hsq 2] at ht
    exact mul_right_cancel₀ (pow_ne_zero 2 (hfull 2)) ht
  have h02 : a 0*a 2 = b 0*b 2 := by
    have hh := he 1
    rw [D.readouts_eq,D.readouts_eq] at hh
    change ((D.cutoff n).factorial : ℝ)^4 * (a 0*a 2*(a 1)^2) =
      ((D.cutoff n).factorial : ℝ)^4 * (b 0*b 2*(b 1)^2) at hh
    have ht := mul_left_cancel₀ hP hh
    rw [← hsq 1] at ht
    exact mul_right_cancel₀ (pow_ne_zero 2 (hfull 1)) ht
  have h12 : a 1*a 2 = b 1*b 2 := by
    have hh := he 0
    rw [D.readouts_eq,D.readouts_eq] at hh
    change ((D.cutoff n).factorial : ℝ)^4 * (a 1*a 2*(a 0)^2) =
      ((D.cutoff n).factorial : ℝ)^4 * (b 1*b 2*(b 0)^2) at hh
    have ht := mul_left_cancel₀ hP hh
    rw [← hsq 0] at ht
    exact mul_right_cancel₀ (pow_ne_zero 2 (hfull 0)) ht
  apply common_of_products
  intro i j
  fin_cases i <;> fin_cases j
  · change a 0*a 0 = b 0*b 0
    simpa only [pow_two] using hsq 0
  · exact h01
  · exact h02
  · change a 1*a 0 = b 1*b 0
    simpa only [mul_comm] using h01
  · change a 1*a 1 = b 1*b 1
    simpa only [pow_two] using hsq 1
  · exact h12
  · change a 2*a 0 = b 2*b 0
    simpa only [mul_comm] using h02
  · change a 2*a 1 = b 2*b 1
    simpa only [mul_comm] using h12
  · change a 2*a 2 = b 2*b 2
    simpa only [pow_two] using hsq 2

private def flip (a : Fin 3 → ℝ) (i j : Fin 3) : ℝ := if j = i then -a j else a j

private theorem flip_squares (a : Fin 3 → ℝ) (i j : Fin 3) :
    (a j)^2 = (flip a i j)^2 := by
  unfold flip
  split_ifs <;> ring

private theorem flip_not_common (a : Fin 3 → ℝ) (i j : Fin 3)
    (hij : i ≠ j) (hi : a i ≠ 0) (hj : a j ≠ 0) : ¬ CommonSign a (flip a i) := by
  rintro (he | he)
  · have hh := he i
    simp only [flip,ite_true] at hh
    exact hi (by linarith)
  · have hh := he j
    simp only [flip,if_neg (Ne.symm hij)] at hh
    exact hj (by linarith)

theorem observations_mono (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ)
    {m k : ℕ} (hk : k ≤ m) (h : D.ObservationsThrough n a b m) :
    D.ObservationsThrough n a b k :=
  ⟨h.1,fun j hj => h.2 j (hj.trans hk)⟩

def RecoveryDegree (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (m : ℕ) : Prop :=
  ∀ b, D.ObservationsThrough n a b m → CommonSign a b

/-- Exact support-dependent observation degree, with every zero case included. -/
theorem recoveryDegree_iff (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (m : ℕ) :
    D.RecoveryDegree n a m ↔ AtMostOne a ∨ (Full a ∧ 4 ≤ m) ∨ 6 ≤ m := by
  constructor
  · intro hrec
    by_cases hsingle : AtMostOne a
    · exact Or.inl hsingle
    by_cases h6 : 6 ≤ m
    · exact Or.inr (Or.inr h6)
    have h5 : m ≤ 5 := by omega
    unfold AtMostOne at hsingle
    push Not at hsingle
    obtain ⟨i,j,hij,hi,hj⟩ := hsingle
    have hbad := flip_not_common a i j hij hi hj
    by_cases hfull : Full a
    · by_cases h4 : 4 ≤ m
      · exact Or.inr (Or.inl ⟨hfull,h4⟩)
      · have h3 : m ≤ 3 := by omega
        exact False.elim (hbad (hrec (flip a i) (D.observations_mono n a (flip a i) h3
          (D.through_three_of_squares n a (flip a i) (flip_squares a i)))))
    · have hz : ∃ k, a k = 0 := by simpa only [Full,not_forall,not_not] using hfull
      exact False.elim (hbad (hrec (flip a i) (D.observations_mono n a (flip a i) h5
        (D.through_five_of_missing_mode n a (flip a i) (flip_squares a i) hz))))
  · rintro (hone | ⟨hfull,h4⟩ | h6) b hobs
    · exact common_of_atMostOne a b hone ((D.affine_iff_squares n a b).mp hobs.1)
    · exact D.common_of_full_quartic n a b hfull
        ((D.affine_iff_squares n a b).mp hobs.1) (hobs.2 4 h4)
    · exact (D.sixth_iff_common n a b).mp (hobs.2 6 h6)

private theorem moment_of_translate (N : ℕ) (c e : ℕ → ℝ) (t : ℕ)
    (he : ∀ k, sieveSeq N e k = sieveSeq N c (k+t))
    {m : ℕ} (h : Fin m → ℕ) : translatedMoment N e h = translatedMoment N c h := by
  have hf (x : ZMod N.factorial) :
      residueSignal N (fun d => (e d : ℂ)) x =
        residueSignal N (fun d => (c d : ℂ)) (x+t) := by
    have hx : x+(t : ZMod N.factorial) = ((x.val+t : ℕ) : ZMod N.factorial) := by simp
    have hs := residueSignal_sieveSeq N e x.val
    rw [ZMod.natCast_zmod_val] at hs
    rw [hs,hx,residueSignal_sieveSeq,he]
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq,translatedMoment_complex_eq]
  unfold translationMoment
  simp_rw [hf]
  apply congrArg (fun z : ℂ => (N.factorial : ℂ)⁻¹*z)
  refine Fintype.sum_equiv (Equiv.addRight (t : ZMod N.factorial)) _ _ (fun x => ?_)
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  change x+(h i : ZMod N.factorial)+(t : ZMod N.factorial) =
    (x+(t : ZMod N.factorial))+(h i : ZMod N.factorial)
  ring

/-- The residual common sign is exactly translation equivalence of actual sieve signals. -/
theorem translation_iff_common (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ) :
    (∃ t : ℕ, ∀ k, sieveSeq (D.cutoff n) (D.weights n b) k =
      sieveSeq (D.cutoff n) (D.weights n a) (k+t)) ↔ CommonSign a b := by
  constructor
  · rintro ⟨t,ht⟩
    apply (D.sixth_iff_common n a b).mp
    intro h
    exact (moment_of_translate _ _ _ t ht h).symm
  · rintro (he | he)
    · refine ⟨0,?_⟩
      intro k
      rw [funext he,Nat.add_zero]
    · refine ⟨D.halfPeriod,?_⟩
      intro k
      rw [funext he,D.signal_neg,D.signal_antiperiod,neg_neg]

/-- Sharp recovery modulo actual integer translation: zero, four, or six additional degrees. -/
theorem sharp_family_observation_order (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (m : ℕ) :
    (∀ b, D.ObservationsThrough n a b m →
      ∃ t : ℕ, ∀ k, sieveSeq (D.cutoff n) (D.weights n b) k =
        sieveSeq (D.cutoff n) (D.weights n a) (k+t)) ↔
      AtMostOne a ∨ (Full a ∧ 4 ≤ m) ∨ 6 ≤ m := by
  simp_rw [D.translation_iff_common n a]
  exact D.recoveryDegree_iff n a m

/-- The same sharp degree holds against arbitrary real sieve weights, with no support premise. -/
theorem sharp_observation_order (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (m : ℕ) :
    (∀ e : ℕ → ℝ,
      (∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t =
        affineMoment (D.cutoff n) e s t) →
      (∀ k ≤ m, ∀ h : Fin k → ℕ,
        translatedMoment (D.cutoff n) (D.weights n a) h =
          translatedMoment (D.cutoff n) e h) →
      ∃ t : ℕ, ∀ k, sieveSeq (D.cutoff n) e k =
        sieveSeq (D.cutoff n) (D.weights n a) (k+t)) ↔
      AtMostOne a ∨ (Full a ∧ 4 ≤ m) ∨ 6 ≤ m := by
  constructor
  · intro hall
    apply (D.sharp_family_observation_order n a m).mp
    intro b hb
    exact hall (D.weights n b) hb.1 hb.2
  · intro hdegree e haff hm
    obtain ⟨b,hb⟩ := D.affine_partner_realization n a e haff
    have hobs : D.ObservationsThrough n a b m := by
      constructor
      · intro s t
        simpa only [affineMoment,hb] using haff s t
      · intro k hk h
        simpa only [translatedMoment,hb] using hm k hk h
    obtain ⟨t,ht⟩ := (D.sharp_family_observation_order n a m).mpr hdegree b hobs
    exact ⟨t,fun k => (hb k).trans (ht k)⟩

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CoprimeOverlap.Triangle
