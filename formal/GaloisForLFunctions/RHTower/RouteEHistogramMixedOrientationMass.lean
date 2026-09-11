import GaloisForLFunctions.RHTower.RouteEHistogramWindowMass
import Mathlib.Logic.Equiv.Prod

/-!
# Window mass for singleton histories with arbitrary factor orientations

Freezing one orientation class preserves the integer spectator aperture.
At least half of the nonconstant coordinates have a common orientation;
complementing all bits exchanges the two biases without changing variance.
The resulting finite bound tends to zero at growing binomial variance and
transfers to the original histogram counts, including admission of every slot.

This excludes a negligible-discard repair of the complete integer-factor
singleton class. It neither constructs an independently conditioned source
nor supplies signed Möbius covariance control. Only changing physical factors
count toward the variance.
-/

open Finset Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.IntegerCubeAperture

variable {C : Type*} [Fintype C] [DecidableEq C]

def activeSetEquiv : (C → Bool) ≃ Finset C where
  toFun := activeSet
  invFun s c := decide (c ∈ s)
  left_inv x := ((activeSet_eq_iff x (activeSet x)).mp rfl).symm
  right_inv s := (activeSet_eq_iff _ s).mpr rfl

def boolWeight (p : ℝ) (x : C → Bool) : ℝ := ∏ c, if x c then p else 1-p

def boolCorner (value : C → Bool → ℕ) (x : C → Bool) : ℕ := ∏ c, value c (x c)

def boolWindowMass (p : ℝ) (value : C → Bool → ℕ) (L U c : ℝ) : ℝ :=
  ∑ x : C → Bool, if c*(boolCorner value x : ℝ) ∈ Set.Icc L U then boolWeight p x else 0

omit [DecidableEq C] in
theorem boolWeight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : C → Bool) :
    0 ≤ boolWeight p x := by
  apply prod_nonneg
  intro i hi
  split_ifs <;> linarith

theorem sum_boolWeight (p : ℝ) : ∑ x : C → Bool, boolWeight p x = 1 := by
  unfold boolWeight
  have h := Fintype.prod_sum (fun (_ : C) (b : Bool) => if b then p else 1-p)
  simpa [Fintype.sum_bool] using h.symm

theorem boolWeight_eq_cornerWeight (p : ℝ) (x : C → Bool) :
    boolWeight p x = p^(activeSet x).card*(1-p)^(Fintype.card C-(activeSet x).card) := by
  unfold boolWeight
  rw [prod_ite]
  have h1 : univ.filter (fun i => x i = true) = activeSet x := rfl
  have h2 : univ.filter (fun i => ¬x i = true) = (activeSet x)ᶜ := by ext; simp [activeSet]
  rw [h1,h2]
  simp only [prod_const,card_compl]

theorem boolCorner_eq_cornerProduct (value : C → Bool → ℕ) (x : C → Bool) :
    boolCorner value x = cornerProduct (fun i => value i false) (fun i => value i true) (activeSet x) := by
  unfold boolCorner cornerProduct
  apply prod_congr rfl
  intro i hi
  cases hx : x i <;> simp [activeSet,hx]

theorem boolWindowMass_eq_subset (p : ℝ) (value : C → Bool → ℕ) (L U c : ℝ) :
    boolWindowMass p value L U c =
      ∑ s ∈ (univ.filter fun s : Finset C =>
        c*(cornerProduct (fun i => value i false) (fun i => value i true) s : ℝ) ∈ Set.Icc L U),
        p^s.card*(1-p)^(Fintype.card C-s.card) := by
  unfold boolWindowMass
  rw [← Equiv.sum_comp (activeSetEquiv (C:=C)).symm]
  rw [sum_filter]
  apply sum_congr rfl
  intro s hs
  have he : activeSet ((activeSetEquiv (C:=C)).symm s) = s :=
    (activeSetEquiv (C:=C)).apply_symm_apply s
  simp only [boolCorner_eq_cornerProduct,boolWeight_eq_cornerWeight,he]

theorem boolWindowMass_increasing_bound (p : ℝ) (value : C → Bool → ℕ) (L W c : ℝ)
    (ha : ∀ i, 1 ≤ value i false) (hab : ∀ i, value i false < value i true)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hc : 1 ≤ c) (hwidth : W^3 < 27*L^2) :
    boolWindowMass p value L (L+W) c ≤
      3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare p (1-p) (Fintype.card C)) := by
  rw [boolWindowMass_eq_subset]
  exact integer_window_spectator_bernoulli_mass_bound _ _ L W c p ha hab hL hW hc hwidth

omit [DecidableEq C] in
theorem boolWeight_split (p : ℝ) (P : C → Prop) [DecidablePred P]
    (y : {i // P i} → Bool) (z : {i // ¬P i} → Bool) :
    boolWeight p ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (y,z)) =
      boolWeight p y*boolWeight p z := by
  unfold boolWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  congr 1 <;> apply prod_congr rfl <;> intro i hi <;>
    simp [Equiv.piEquivPiSubtypeProd,i.2]

omit [DecidableEq C] in
theorem boolCorner_split (value : C → Bool → ℕ) (P : C → Prop) [DecidablePred P]
    (y : {i // P i} → Bool) (z : {i // ¬P i} → Bool) :
    boolCorner value ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (y,z)) =
      boolCorner (fun i : {i // P i} => value i) y *
        boolCorner (fun i : {i // ¬P i} => value i) z := by
  unfold boolCorner
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  congr 1 <;> apply prod_congr rfl <;> intro i hi <;>
    simp [Equiv.piEquivPiSubtypeProd,i.2]

theorem boolWindowMass_split (p : ℝ) (value : C → Bool → ℕ) (L U c : ℝ)
    (P : C → Prop) [DecidablePred P] :
    boolWindowMass p value L U c =
      ∑ z : {i // ¬P i} → Bool, boolWeight p z *
        boolWindowMass p (fun i : {i // P i} => value i) L U
          (c*(boolCorner (fun i : {i // ¬P i} => value i) z : ℝ)) := by
  unfold boolWindowMass
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm,
    Fintype.sum_prod_type,sum_comm]
  apply sum_congr rfl
  intro z hz
  rw [mul_sum]
  apply sum_congr rfl
  intro y hy
  rw [boolWeight_split,boolCorner_split,Nat.cast_mul]
  have he : c*((boolCorner (fun i : {i // P i} => value i) y : ℝ)*
      (boolCorner (fun i : {i // ¬P i} => value i) z : ℝ)) =
      (c*(boolCorner (fun i : {i // ¬P i} => value i) z : ℝ))*
        (boolCorner (fun i : {i // P i} => value i) y : ℝ) := by ring
  rw [he]
  split_ifs <;> ring

theorem boolWindowMass_increasing_block_bound (p : ℝ) (value : C → Bool → ℕ) (L W c : ℝ)
    (P : C → Prop) [DecidablePred P]
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hvalue : ∀ i b, 1 ≤ value i b)
    (hincreasing : ∀ i, P i → value i false < value i true)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hc : 1 ≤ c) (hwidth : W^3 < 27*L^2) :
    boolWindowMass p value L (L+W) c ≤
      3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare p (1-p)
        (Fintype.card {i // P i})) := by
  rw [boolWindowMass_split p value L (L+W) c P]
  let K := 3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare p (1-p)
    (Fintype.card {i // P i}))
  calc
    _ ≤ ∑ z : {i // ¬P i} → Bool, boolWeight p z*K := by
      apply sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (boolWeight_nonneg p hp0 hp1 z)
      have hn : 1 ≤ boolCorner (fun i : {i // ¬P i} => value i) z :=
        Nat.succ_le_of_lt (prod_pos fun i _ => hvalue i (z i))
      have hr : (1:ℝ) ≤ (boolCorner (fun i : {i // ¬P i} => value i) z : ℝ) := by exact_mod_cast hn
      exact boolWindowMass_increasing_bound p _ L W _
        (fun i => hvalue i false) (fun i => hincreasing i i.2) hL hW
        (by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hr)]) hwidth
    _ = _ := by rw [← sum_mul,sum_boolWeight]; simp [K]

def boolComplementEquiv : (C → Bool) ≃ (C → Bool) where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; exact Bool.not_not _
  right_inv x := by funext i; exact Bool.not_not _

theorem boolWindowMass_complement (p : ℝ) (value : C → Bool → ℕ) (L U c : ℝ) :
    boolWindowMass p value L U c =
      boolWindowMass (1-p) (fun i b => value i (!b)) L U c := by
  unfold boolWindowMass
  rw [← Equiv.sum_comp (boolComplementEquiv (C:=C))]
  apply sum_congr rfl
  intro x hx
  have hvalue : boolCorner value (boolComplementEquiv x) =
      boolCorner (fun i b => value i (!b)) x := rfl
  rw [hvalue]
  split_ifs
  · unfold boolWeight
    apply prod_congr rfl
    intro i hi
    cases hb : x i <;> simp [boolComplementEquiv,hb]
  · rfl

/-- A single orientation class carries at least half of the nonconstant coordinates. -/
theorem boolWindowMass_orientation_bound (p : ℝ) (value : C → Bool → ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hvalue : ∀ i b, 1 ≤ value i b)
    (hchange : ∀ i, value i false ≠ value i true) :
    ∃ q : ℝ, ∃ k : ℕ, 0 ≤ q ∧ q ≤ 1 ∧ q*(1-q) = p*(1-p) ∧
      Fintype.card C ≤ 2*k ∧
      ∀ L W c : ℝ, 0 ≤ L → 0 ≤ W → 1 ≤ c → W^3 < 27*L^2 →
        boolWindowMass p value L (L+W) c ≤
          3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare q (1-q) k) := by
  let P : C → Prop := fun i => value i false < value i true
  have hcard := Fintype.card_congr (Equiv.sumCompl P)
  rw [Fintype.card_sum] at hcard
  by_cases hlarge : Fintype.card C ≤ 2*Fintype.card {i // P i}
  · refine ⟨p,Fintype.card {i // P i},hp0,hp1,rfl,hlarge,?_⟩
    intro L W c hL hW hc hwidth
    exact boolWindowMass_increasing_block_bound p value L W c P hp0 hp1 hvalue
      (fun _ hi => hi) hL hW hc hwidth
  · refine ⟨1-p,Fintype.card {i // ¬P i},by linarith,by linarith,by ring,by omega,?_⟩
    intro L W c hL hW hc hwidth
    rw [boolWindowMass_complement]
    apply boolWindowMass_increasing_block_bound (1-p) (fun i b => value i (!b))
      L W c (fun i => ¬P i) (by linarith) (by linarith) (fun i b => hvalue i (!b))
      _ hL hW hc hwidth
    intro i hi
    have hn := hchange i
    dsimp [P] at hi
    simp only [Bool.not_false,Bool.not_true]
    omega

/-- Reversing factor orientations does not prevent loss of mass in the growing window. -/
theorem tendsto_growing_window_bool_mass_zero
    (d : ℕ → ℕ) (value : ∀ n, Fin (d n) → Bool → ℕ) (X c p : ℕ → ℝ)
    (hvalue : ∀ n i b, 1 ≤ value n i b)
    (hchange : ∀ n i, value n i false ≠ value n i true)
    (hc : ∀ n, 1 ≤ c n) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hX : Tendsto X atTop atTop)
    (hvariance : Tendsto (fun n => (d n:ℝ)*p n*(1-p n)) atTop atTop) :
    Tendsto (fun n => boolWindowMass (p n) (value n)
      (X n-Sieve.growingReciprocalMarkerWindow (X n))
      (X n+Sieve.growingReciprocalMarkerWindow (X n)) (c n)) atTop (𝓝 0) := by
  choose q k hq0 hq1 hvar hsize hbound using fun n =>
    boolWindowMass_orientation_bound (p n) (value n) (hp n).1 (hp n).2
      (hvalue n) (hchange n)
  have hselected : Tendsto (fun n => (k n:ℝ)*q n*(1-q n)) atTop atTop := by
    apply Filter.tendsto_atTop_mono _
      (Filter.Tendsto.const_mul_atTop (show (0:ℝ) < 1/2 by norm_num) hvariance)
    intro n
    have hs : (d n:ℝ) ≤ 2*(k n:ℝ) := by
      exact_mod_cast (by simpa only [Fintype.card_fin] using hsize n)
    have hpq : 0 ≤ p n*(1-p n) := mul_nonneg (hp n).1 (sub_nonneg.mpr (hp n).2)
    calc
      (1/2)*((d n:ℝ)*p n*(1-p n)) = ((1/2)*(d n:ℝ))*(p n*(1-p n)) := by ring
      _ ≤ (k n:ℝ)*(p n*(1-p n)) := mul_le_mul_of_nonneg_right (by linarith) hpq
      _ = (k n:ℝ)*q n*(1-q n) := by rw [← hvar n]; ring
  have hupper : ∀ᶠ n in atTop,
      boolWindowMass (p n) (value n)
        (X n-Sieve.growingReciprocalMarkerWindow (X n))
        (X n+Sieve.growingReciprocalMarkerWindow (X n)) (c n) ≤
      3*Real.sqrt (GaloisForLFunctions.HTGeometry.bernsteinRowSquare (q n) (1-q n) (k n)) := by
    filter_upwards [hX.eventually growing_window_aperture] with n hn
    have he : X n-Sieve.growingReciprocalMarkerWindow (X n)+
        2*Sieve.growingReciprocalMarkerWindow (X n) =
        X n+Sieve.growingReciprocalMarkerWindow (X n) := by ring
    simpa only [he] using hbound n
      (X n-Sieve.growingReciprocalMarkerWindow (X n))
      (2*Sieve.growingReciprocalMarkerWindow (X n)) (c n)
      (by linarith [hn.2.1]) (by linarith [hn.1]) (hc n) hn.2.2
  have hlimit := ((tendsto_binomial_rowSquare_zero k q
    (fun n => ⟨hq0 n,hq1 n⟩) hselected).sqrt).const_mul (3:ℝ)
  refine squeeze_zero' ?_ hupper ?_
  · filter_upwards with n
    apply sum_nonneg
    intro x hx
    split_ifs
    · exact boolWeight_nonneg _ (hp n).1 (hp n).2 _
    · rfl
  · simpa only [Real.sqrt_zero,mul_zero] using hlimit

/-- Exact histogram admission mass in Bool-product coordinates, without an orientation assumption. -/
theorem histogram_anchor_boolWindowMass (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ i, ∑ z, k i z = m+1) (hone : ∀ i, k i true = 1)
    (r : Fin (m+1)) (a b : C → ℕ) (L U : ℝ) :
    (((routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).filter fun h =>
      routeEComponentSlotReceiver (fun _ : C => Bool)
        (fun i z => if z then (b i:ℝ) else (a i:ℝ)) h r ∈ Set.Icc L U).card : ℝ) /
      (routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).card =
      boolWindowMass (1/((m+1:ℕ):ℝ)) (fun i z => if z then b i else a i) L U 1 := by
  simpa only [boolWindowMass_eq_subset,one_mul,Bool.false_eq_true,↓reduceIte] using
    histogram_anchor_window_mass m k hk hone r a b L U

/-- Arbitrary orientations: the admitted fraction of literal singleton histories vanishes. -/
theorem tendsto_growing_window_histogram_mixed_mass_zero
    (d m : ℕ → ℕ) (k : ∀ n, Fin (d n) → Bool → ℕ)
    (a b : ∀ n, Fin (d n) → ℕ) (X : ℕ → ℝ) (r : ∀ n, Fin (m n+1))
    (hk : ∀ n i, ∑ z, k n i z = m n+1) (hone : ∀ n i, k n i true = 1)
    (ha : ∀ n i, 1 ≤ a n i) (hb : ∀ n i, 1 ≤ b n i)
    (hchange : ∀ n i, a n i ≠ b n i) (hX : Tendsto X atTop atTop)
    (hvariance : Tendsto (fun n => (d n:ℝ)*(1/((m n+1:ℕ):ℝ))*
      (1-1/((m n+1:ℕ):ℝ))) atTop atTop) :
    Tendsto (fun n =>
      (((routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).filter fun h =>
        routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) h (r n) ∈
            Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
              (X n+Sieve.growingReciprocalMarkerWindow (X n))).card : ℝ) /
        (routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).card)
      atTop (𝓝 0) := by
  have hp (n : ℕ) : 0 ≤ (1/((m n+1:ℕ):ℝ)) ∧ (1/((m n+1:ℕ):ℝ)) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast Nat.succ_pos (m n)
  have ht := tendsto_growing_window_bool_mass_zero d
    (fun n i z => if z then b n i else a n i) X (fun _ => 1)
    (fun n => 1/((m n+1:ℕ):ℝ))
    (by intro n i z; cases z <;> simp [ha,hb])
    (by simpa using hchange) (by intro; rfl) hp hX hvariance
  simpa only [histogram_anchor_boolWindowMass _ _ (hk _) (hone _)] using ht

/-- Requiring every slot to lie in the physical window also retains asymptotically zero mass. -/
theorem tendsto_growing_window_histogram_all_slots_mass_zero
    (d m : ℕ → ℕ) (k : ∀ n, Fin (d n) → Bool → ℕ)
    (a b : ∀ n, Fin (d n) → ℕ) (X : ℕ → ℝ)
    (hk : ∀ n i, ∑ z, k n i z = m n+1) (hone : ∀ n i, k n i true = 1)
    (ha : ∀ n i, 1 ≤ a n i) (hb : ∀ n i, 1 ≤ b n i)
    (hchange : ∀ n i, a n i ≠ b n i) (hX : Tendsto X atTop atTop)
    (hvariance : Tendsto (fun n => (d n:ℝ)*(1/((m n+1:ℕ):ℝ))*
      (1-1/((m n+1:ℕ):ℝ))) atTop atTop) :
    Tendsto (fun n =>
      (((routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).filter fun h =>
        ∀ r, routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) h r ∈
            Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
              (X n+Sieve.growingReciprocalMarkerWindow (X n))).card : ℝ) /
        (routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).card)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => by positivity) _
    (tendsto_growing_window_histogram_mixed_mass_zero d m k a b X (fun _ => 0)
      hk hone ha hb hchange hX hvariance)
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (show
      ((routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).filter fun h =>
        ∀ r, routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) h r ∈
            Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
              (X n+Sieve.growingReciprocalMarkerWindow (X n))).card ≤
      ((routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).filter fun h =>
        routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) h 0 ∈
            Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
              (X n+Sieve.growingReciprocalMarkerWindow (X n))).card from
    card_le_card (by intro h hh; exact mem_filter.mpr ⟨(mem_filter.mp hh).1,(mem_filter.mp hh).2 0⟩))

end RHTower.IntegerCubeAperture
