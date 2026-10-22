import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ValuatedPluckerGram
import GaloisForLFunctions.RHTower.Deninger.DeningerTestHeightBridge

/-!
# Adelic Plücker history mechanics

One diagonal intervention has four forced shadows: relative Plücker response, an all-place Kummer
current, a complete relative height, and an Archimedean Gram observer.  The response reconstructs
the relative character; its place sum is zero; its complete height is bounded exactly for periodic
projective history; and a unitary Archimedean realization can keep the full Gram matrix static
while the adelic height grows exactly linearly.

This module certifies the source-independent theorem behind
`docs/drafts/pipeline/2-fully-proven/universal-law-field/adelic-plucker-history-mechanics/`.
-/

namespace HTGeometry

open RHTower

noncomputable section

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι]

/-- Relative diagonal character exposed by a Plücker exchange. -/
def relativePluckerResponse (q : ι → K) (b i : ι) (m : ℕ) : K :=
  (q i / q b) ^ m

/-- Complete height of all relative responses in one projective chart. -/
def completeExchangeHeight (q : ι → K) (b : ι) (m : ℕ) : ℝ :=
  ∑ i, Height.logHeight₁ (relativePluckerResponse q b i m)

/-- Time-one relative packet. -/
def relativePluckerPacket (q : ι → K) (b : ι) : ι → K :=
  fun i => q i / q b

/-- A nonzero initial Plücker packet evolved by diagonal characters. -/
def pluckerPacket (p q : ι → K) (m : ℕ) : ι → K :=
  fun i => p i * q i ^ m

/-- Projective equality of two finite packets. -/
def ProjectivelyEquivalent (x y : ι → K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ ∀ i, x i = c * y i

/-- Periodicity from time zero of the full evolved Plücker packet. -/
def PluckerPacketPeriodic (p q : ι → K) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∀ m : ℕ,
    ProjectivelyEquivalent (pluckerPacket p q (m + d)) (pluckerPacket p q m)

/-- Periodicity from time zero of the normalized relative packet. -/
def RelativePacketPeriodic (q : ι → K) (b : ι) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∀ m : ℕ,
    (fun i => relativePluckerResponse q b i (m + d)) =
      fun i => relativePluckerResponse q b i m

/-- Absolute logarithmic projective height of the evolved Plücker packet. -/
def pluckerProjectiveHeight (p q : ι → K) (m : ℕ) : ℝ :=
  Height.logHeight (pluckerPacket p q m)

/-- Initial packet normalized in one nonzero projective chart. -/
def normalizedInitialPacket (p : ι → K) (b : ι) : ι → K :=
  fun i => p i / p b

/-- **Exact complete-height law.**  Complete response height grows exactly linearly. -/
theorem completeExchangeHeight_exact_growth (q : ι → K) (b : ι) (m : ℕ) :
    completeExchangeHeight q b m = m * completeExchangeHeight q b 1 := by
  simp only [completeExchangeHeight, relativePluckerResponse, Height.logHeight₁_pow,
    pow_one, Finset.mul_sum]

theorem completeExchangeHeight_nonneg (q : ι → K) (b : ι) (m : ℕ) :
    0 ≤ completeExchangeHeight q b m := by
  exact Finset.sum_nonneg fun i _ => Height.zero_le_logHeight₁ _

/-- Complete height vanishes exactly when every relative character is torsion. -/
theorem completeExchangeHeight_one_eq_zero_iff
    (q : ι → K) (hq : ∀ i, q i ≠ 0) (b : ι) :
    completeExchangeHeight q b 1 = 0 ↔
      ∀ i, IsOfFinOrder (relativePluckerPacket q b i) := by
  constructor
  · intro h i
    have hterm : Height.logHeight₁ (relativePluckerPacket q b i) = 0 := by
      have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
          0 ≤ Height.logHeight₁ (relativePluckerPacket q b j) := by
        intro j _hj
        exact Height.zero_le_logHeight₁ _
      have hsum : ∑ j, Height.logHeight₁ (relativePluckerPacket q b j) = 0 := by
        simpa [completeExchangeHeight, relativePluckerResponse, relativePluckerPacket] using h
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
    exact (deningerLogHeightZero_iff_isOfFinOrder (div_ne_zero (hq i) (hq b))).mp hterm
  · intro h
    simp only [completeExchangeHeight, relativePluckerResponse, pow_one]
    apply Finset.sum_eq_zero
    intro i _hi
    exact (deningerLogHeightZero_iff_isOfFinOrder (div_ne_zero (hq i) (hq b))).mpr (h i)

omit [NumberField K] [Fintype ι] in
/-- A normalized packet is periodic exactly when it is a finite-order element of the product
group. -/
theorem relativePacketPeriodic_iff_isOfFinOrder
    (q : ι → K) (b : ι) :
    RelativePacketPeriodic q b ↔ IsOfFinOrder (relativePluckerPacket q b) := by
  constructor
  · rintro ⟨d, hd, hperiod⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨d, hd, ?_⟩
    funext i
    have hi := congrFun (hperiod 0) i
    simpa [relativePluckerResponse, relativePluckerPacket] using hi
  · intro h
    obtain ⟨d, hd, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
    refine ⟨d, hd, fun m => ?_⟩
    funext i
    have hi := congrFun hpow i
    have hi' : (q i / q b) ^ d = 1 := by
      simpa [relativePluckerPacket] using hi
    simp only [relativePluckerResponse, pow_add]
    rw [hi', mul_one]

/-- Complete height zero is exactly periodic relative history. -/
theorem completeExchangeHeight_zero_iff_periodic
    (q : ι → K) (hq : ∀ i, q i ≠ 0) (b : ι) :
    completeExchangeHeight q b 1 = 0 ↔ RelativePacketPeriodic q b := by
  rw [completeExchangeHeight_one_eq_zero_iff q hq b,
    relativePacketPeriodic_iff_isOfFinOrder]
  exact ⟨IsOfFinOrder.pi, fun h i => h.apply i⟩

omit [NumberField K] [Fintype ι] in
/-- Relative periodicity is equivalent to projective periodicity of every nonzero initial Plücker
packet. -/
theorem relativePacketPeriodic_iff_pluckerPacketPeriodic
    (p q : ι → K) (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0) (b : ι) :
    RelativePacketPeriodic q b ↔ PluckerPacketPeriodic p q := by
  constructor
  · rintro ⟨d, hd, hrel⟩
    refine ⟨d, hd, fun m => ⟨q b ^ d, pow_ne_zero d (hq b), fun i => ?_⟩⟩
    have hratio := congrFun (hrel 0) i
    have hqpow : q i ^ d = q b ^ d := by
      have hdiv : (q i ^ d) / (q b ^ d) = 1 := by
        simpa [relativePluckerResponse, div_pow] using hratio
      exact (div_eq_one_iff_eq (pow_ne_zero d (hq b))).mp hdiv
    simp only [pluckerPacket, pow_add]
    rw [hqpow]
    ring
  · rintro ⟨d, hd, hproj⟩
    refine ⟨d, hd, fun m => ?_⟩
    obtain ⟨c, hc, hpacket⟩ := hproj 0
    funext i
    have hi := hpacket i
    have hb := hpacket b
    have hiq : q i ^ d = c := by
      have hi' : p i * q i ^ d = p i * c := by
        simpa [pluckerPacket, mul_comm] using hi
      exact mul_left_cancel₀ (hp i) hi'
    have hbq : q b ^ d = c := by
      have hb' : p b * q b ^ d = p b * c := by
        simpa [pluckerPacket, mul_comm] using hb
      exact mul_left_cancel₀ (hp b) hb'
    have hratio : (q i / q b) ^ d = 1 := by
      rw [div_pow, hiq, hbq, div_self hc]
    simp only [relativePluckerResponse, pow_add]
    rw [hratio, mul_one]

/-- A linearly growing nonnegative complete height is bounded exactly when its initial value is
zero. -/
theorem completeExchangeHeight_bounded_iff_zero
    (q : ι → K) (b : ι) :
    (∃ C : ℝ, ∀ m : ℕ, completeExchangeHeight q b m ≤ C) ↔
      completeExchangeHeight q b 1 = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have hpos : 0 < completeExchangeHeight q b 1 :=
      lt_of_le_of_ne (completeExchangeHeight_nonneg q b 1) (Ne.symm hne)
    obtain ⟨m, hm⟩ := exists_nat_gt (C / completeExchangeHeight q b 1)
    have hstrict : C < (m : ℝ) * completeExchangeHeight q b 1 :=
      (div_lt_iff₀ hpos).mp hm
    have hbound := hC m
    rw [completeExchangeHeight_exact_growth] at hbound
    linarith
  · intro hzero
    refine ⟨0, fun m => ?_⟩
    rw [completeExchangeHeight_exact_growth, hzero, mul_zero]

/-- **Northcott/Kummer rigidity.**  Bounded complete relative history is exactly periodic
projective history. -/
theorem completeExchangeHeight_bounded_iff_periodic
    (q : ι → K) (hq : ∀ i, q i ≠ 0) (b : ι) :
    (∃ C : ℝ, ∀ m : ℕ, completeExchangeHeight q b m ≤ C) ↔
      RelativePacketPeriodic q b := by
  rw [completeExchangeHeight_bounded_iff_zero,
    completeExchangeHeight_zero_iff_periodic q hq b]

/-- Every coordinate ratio height is bounded by the full projective packet height. -/
theorem coordinateRatio_height_le_projectiveHeight
    (x : ι → K) (i b : ι) :
    Height.logHeight₁ (x i / x b) ≤ Height.logHeight x := by
  rw [Height.logHeight₁_div_eq_logHeight]
  have heq : (fun k : Fin 2 => x (![i, b] k)) = ![x i, x b] := by
    funext k
    fin_cases k <;> rfl
  rw [← heq]
  exact Height.logHeight_comp_le ![i, b] x

/-- Projective height is the height of the normalized initial packet times the relative response
packet. -/
theorem pluckerProjectiveHeight_eq_normalized
    (p q : ι → K) (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (b : ι) (m : ℕ) :
    pluckerProjectiveHeight p q m =
      Height.logHeight (normalizedInitialPacket p b *
        fun i => relativePluckerResponse q b i m) := by
  have hbase : pluckerPacket p q m b ≠ 0 :=
    mul_ne_zero (hp b) (pow_ne_zero m (hq b))
  rw [pluckerProjectiveHeight,
    ← Height.logHeight_smul_eq_logHeight (pluckerPacket p q m) (inv_ne_zero hbase)]
  apply congrArg Height.logHeight
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, pluckerPacket, normalizedInitialPacket,
    Pi.mul_apply, relativePluckerResponse]
  field_simp
  ring

/-- A bound for projective packet height gives an explicit bound for complete exchange height. -/
theorem completeExchangeHeight_le_projective_bound
    (p q : ι → K) (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (b : ι) (m : ℕ) {C : ℝ} (hC : pluckerProjectiveHeight p q m ≤ C) :
    completeExchangeHeight q b m ≤
      (∑ i, Height.logHeight₁ (p i / p b)) + Fintype.card ι * C := by
  rw [completeExchangeHeight]
  calc
    (∑ i, Height.logHeight₁ (relativePluckerResponse q b i m))
        ≤ ∑ i, (Height.logHeight₁ (p i / p b) + C) := by
          apply Finset.sum_le_sum
          intro i _hi
          have hpacket :
              relativePluckerResponse q b i m =
                (p i / p b)⁻¹ *
                  (pluckerPacket p q m i / pluckerPacket p q m b) := by
            simp only [relativePluckerResponse, pluckerPacket]
            field_simp [hp i, hp b, hq i, hq b]
            rw [div_pow]
            field_simp [hq b]
          rw [hpacket]
          calc
            Height.logHeight₁ ((p i / p b)⁻¹ *
                (pluckerPacket p q m i / pluckerPacket p q m b))
                ≤ Height.logHeight₁ (p i / p b)⁻¹ +
                    Height.logHeight₁
                      (pluckerPacket p q m i / pluckerPacket p q m b) :=
              Height.logHeight₁_mul_le _ _
            _ = Height.logHeight₁ (p i / p b) +
                    Height.logHeight₁
                      (pluckerPacket p q m i / pluckerPacket p q m b) := by
              rw [Height.logHeight₁_inv]
            _ ≤ Height.logHeight₁ (p i / p b) +
                    pluckerProjectiveHeight p q m := by
              exact add_le_add le_rfl
                (coordinateRatio_height_le_projectiveHeight
                  (pluckerPacket p q m) i b)
            _ ≤ Height.logHeight₁ (p i / p b) + C := add_le_add le_rfl hC
    _ = (∑ i, Height.logHeight₁ (p i / p b)) + Fintype.card ι * C := by
      rw [Finset.sum_add_distrib]
      simp

/-- Periodic relative response gives a uniform bound for the standard absolute projective height
of every evolved Plücker packet. -/
theorem relativePacketPeriodic_projectiveHeight_bounded
    (p q : ι → K) (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (b : ι) (hper : RelativePacketPeriodic q b) :
    ∃ C : ℝ, ∀ m : ℕ, pluckerProjectiveHeight p q m ≤ C := by
  have hfin : IsOfFinOrder (relativePluckerPacket q b) :=
    (relativePacketPeriodic_iff_isOfFinOrder q b).mp hper
  obtain ⟨d, hd, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hrelzero : Height.logHeight (relativePluckerPacket q b) = 0 := by
    have hheight := Height.logHeight_pow (relativePluckerPacket q b) d
    rw [hpow, Height.logHeight_one] at hheight
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    exact (mul_eq_zero.mp hheight.symm).resolve_left hd'.ne'
  refine ⟨Height.logHeight (normalizedInitialPacket p b), fun m => ?_⟩
  rw [pluckerProjectiveHeight_eq_normalized p q hp hq b m]
  calc
    Height.logHeight (normalizedInitialPacket p b *
        fun i => relativePluckerResponse q b i m)
      ≤ Height.logHeight (normalizedInitialPacket p b) +
          Height.logHeight (fun i => relativePluckerResponse q b i m) :=
        Height.logHeight_mul_le _ _
    _ = Height.logHeight (normalizedInitialPacket p b) := by
      have hfun : (fun i => relativePluckerResponse q b i m) =
          relativePluckerPacket q b ^ m := by
        rfl
      rw [hfun, Height.logHeight_pow, hrelzero, mul_zero, add_zero]

/-- **Standard projective Northcott classification.**  Bounded absolute projective height of the
whole evolved packet is exactly periodic relative history. -/
theorem pluckerProjectiveHeight_bounded_iff_periodic
    (p q : ι → K) (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0) (b : ι) :
    (∃ C : ℝ, ∀ m : ℕ, pluckerProjectiveHeight p q m ≤ C) ↔
      RelativePacketPeriodic q b := by
  constructor
  · rintro ⟨C, hC⟩
    apply (completeExchangeHeight_bounded_iff_periodic q hq b).mp
    refine ⟨(∑ i, Height.logHeight₁ (p i / p b)) + Fintype.card ι * C,
      fun m => ?_⟩
    exact completeExchangeHeight_le_projective_bound p q hp hq b m (hC m)
  · exact relativePacketPeriodic_projectiveHeight_bounded p q hp hq b

/-- **Exact exchange reconstruction.**  The normalized cross-ratio of two adjacent evolved minors
is the relative diagonal character to the same power. -/
theorem pluckerExchangeResponse_exact
    {pB pB' uB ui uj : K} (hpB : pB ≠ 0) (hpB' : pB' ≠ 0)
    (huB : uB ≠ 0) (_hui : ui ≠ 0) (m : ℕ) :
    ((pB' * (uB * (uj / ui)) ^ m) * pB) /
        ((pB * uB ^ m) * pB') = (uj / ui) ^ m := by
  field_simp
  rw [show uB * uj / ui = uB * (uj / ui) by ring, mul_pow]

omit [Fintype ι] in
/-- **All-place conservation.**  Every reconstructed exchange character lies in the kernel of the
adelic place sum. -/
theorem exchangeResponse_allPlace_conservation
    (q : ι → K) (hq : ∀ i, q i ≠ 0) (b i : ι) (m : ℕ) :
    deningerPlaceSum K
        (deningerKummerTest K (pow_ne_zero m (div_ne_zero (hq i) (hq b)))) = 0 := by
  exact deningerKummer_sum_eq_zero K _

/-- A coordinate ratio gives a quantitative lower bound for the evolved packet height. -/
theorem exchangeCoordinateHeight_lower
    {α β : K} (hα : α ≠ 0) (m : ℕ) :
    m * Height.logHeight₁ β - Height.logHeight₁ α ≤
      Height.logHeight₁ (α * β ^ m) := by
  have h := Height.logHeight₁_mul_le α⁻¹ (α * β ^ m)
  have hid : α⁻¹ * (α * β ^ m) = β ^ m := by
    field_simp
  rw [hid, Height.logHeight₁_inv, Height.logHeight₁_pow] at h
  linarith

open ConstraintFrameRelativity

variable {r n : ℕ}

/-- Complex phase packet induced by a number-field diagonal character. -/
def adelicPhase (σ : K →+* ℂ) (q : Fin n → K) (m : ℕ) : Fin n → ℂ :=
  fun i => σ (q i) ^ m

omit [NumberField K] in
/-- A unitary diagonal arithmetic intervention leaves the positive Gram observer exactly static. -/
theorem frameGram_adelicPhase_static
    (σ : K →+* ℂ) (T : Matrix (Fin r) (Fin n) ℂ) (q : Fin n → K)
    (hu : ∀ i, σ (q i) * starRingEnd ℂ (σ (q i)) = 1) (m : ℕ) :
    frameGram (starRingEnd ℂ) (T * Matrix.diagonal (adelicPhase σ q m)) =
      frameGram (starRingEnd ℂ) T := by
  apply frameGram_rephase
  intro i
  simp only [adelicPhase, map_pow]
  rw [← mul_pow, hu i, one_pow]

omit [NumberField K] in
/-- The same intervention evolves every Plücker minor by the product of its column characters. -/
theorem frameMinor_adelicPhase
    (σ : K →+* ℂ) (T : Matrix (Fin r) (Fin n) ℂ) (q : Fin n → K)
    (m : ℕ) (c : Fin r → Fin n) :
    frameMinor (T * Matrix.diagonal (adelicPhase σ q m)) c =
      (∏ k, σ (q (c k)) ^ m) * frameMinor T c := by
  simpa [adelicPhase] using frameMinor_rephase T (adelicPhase σ q m) c

/-- **Static-positive/open-adelic prediction.**  A positive Gram observer can be stationary while
one reconstructed arithmetic exchange response has strictly positive, exactly linear height. -/
theorem staticGram_openAdelicHistory
    (σ : K →+* ℂ) (T : Matrix (Fin r) (Fin n) ℂ) (q : Fin n → K)
    (hq : ∀ i, q i ≠ 0)
    (hu : ∀ i, σ (q i) * starRingEnd ℂ (σ (q i)) = 1)
    {b i : Fin n} (hopen : ¬ IsOfFinOrder (q i / q b)) :
    (∀ m : ℕ,
      frameGram (starRingEnd ℂ) (T * Matrix.diagonal (adelicPhase σ q m)) =
        frameGram (starRingEnd ℂ) T) ∧
      0 < Height.logHeight₁ (q i / q b) ∧
      ∀ m : ℕ, Height.logHeight₁ ((q i / q b) ^ m) =
        m * Height.logHeight₁ (q i / q b) := by
  refine ⟨fun m => frameGram_adelicPhase_static σ T q hu m, ?_,
    Height.logHeight₁_pow _⟩
  have hne : Height.logHeight₁ (q i / q b) ≠ 0 := by
    intro hzero
    exact hopen ((deningerLogHeightZero_iff_isOfFinOrder
      (div_ne_zero (hq i) (hq b))).mp hzero)
  exact lt_of_le_of_ne (Height.zero_le_logHeight₁ _) (Ne.symm hne)

/-- **Four-organ fusion capstone.**  One diagonal source intervention simultaneously evolves the
Plücker relation packet, conserves its response across all places, freezes the positive Gram
observer, and opens the complete arithmetic history at an exact linear rate. -/
theorem adelicPluckerFusion_capstone
    (σ : K →+* ℂ) (T : Matrix (Fin r) (Fin n) ℂ) (q : Fin n → K)
    (hq : ∀ i, q i ≠ 0)
    (hu : ∀ i, σ (q i) * starRingEnd ℂ (σ (q i)) = 1)
    {b i : Fin n} (hopen : ¬ IsOfFinOrder (q i / q b)) :
    (∀ (m : ℕ) (c : Fin r → Fin n),
      frameMinor (T * Matrix.diagonal (adelicPhase σ q m)) c =
        (∏ k, σ (q (c k)) ^ m) * frameMinor T c) ∧
    (∀ m : ℕ,
      frameGram (starRingEnd ℂ) (T * Matrix.diagonal (adelicPhase σ q m)) =
        frameGram (starRingEnd ℂ) T) ∧
    (∀ m : ℕ,
      deningerPlaceSum K
        (deningerKummerTest K (pow_ne_zero m (div_ne_zero (hq i) (hq b)))) = 0) ∧
    0 < Height.logHeight₁ (q i / q b) ∧
    ∀ m : ℕ, Height.logHeight₁ ((q i / q b) ^ m) =
      m * Height.logHeight₁ (q i / q b) := by
  rcases staticGram_openAdelicHistory σ T q hq hu hopen with ⟨hgram, hpos, hgrowth⟩
  exact ⟨frameMinor_adelicPhase σ T q, hgram,
    fun m => exchangeResponse_allPlace_conservation q hq b i m,
    hpos, hgrowth⟩

end

end HTGeometry
