import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing

/-!
# The torsion cap in anchored coordinates

The concentration cap counts phase vectors whose coordinate sum is atypically large.  A target
captures a set of phase vectors whose *relative* sums are all large, so translating the captured set
to one of its own members turns the cap into a bound on the captured set itself.

Counting through the `k`-to-one anchoring fibration and summing over the dictionary turns that into
a bound on the easy projective classes, and the resulting bound is exactly the input the prime-torsion
polygon theorem consumes: the exponential smallness of the easy set becomes the counting hypothesis
that produces a hard class, hence an arbitrarily late recurrence cycle whose interior slices are all
hard.
-/

open Real RHTower

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section AnchoredCap

variable {D d k : ℕ}

/-- The additive character of `ZMod k` as a power of the standard primitive root. -/
theorem coe_toCircle_eq_pow [NeZero k] (x : ZMod k) :
    (ZMod.toCircle x : ℂ) = (Complex.exp (2 * π * Complex.I / (k : ℂ))) ^ x.val := by
  have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  rw [ZMod.toCircle_apply, ← Complex.exp_nat_mul]
  congr 1
  field_simp

/-- **The torsion cap in `ZMod` coordinates.**  At most `4 e^{-ε²/(4D)} k^D` phase vectors have
coordinate sum of modulus at least `ε`. -/
theorem card_le_of_forall_norm_toCircle_sum_ge [NeZero k] (hk : 1 < k)
    (S : Finset (Fin D → ZMod k)) {ε : ℝ} (hε : 0 ≤ ε)
    (hS : ∀ u ∈ S, ε ≤ ‖∑ a, (ZMod.toCircle (u a) : ℂ)‖) :
    (S.card : ℝ) ≤ 4 * Real.exp (-ε ^ (2 : ℕ) / (4 * (D : ℝ))) * (k : ℝ) ^ D := by
  classical
  have hζ : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / (k : ℂ))) k :=
    Complex.isPrimitiveRoot_exp k (NeZero.ne k)
  set e : (Fin D → ZMod k) → (Fin D → Fin k) := fun u a => ⟨(u a).val, ZMod.val_lt (u a)⟩ with he
  have hinj : Function.Injective e := by
    intro u v huv
    funext a
    have : (u a).val = (v a).val := congrArg Fin.val (congrFun huv a)
    exact ZMod.val_injective k this
  have hsum : ∀ u : Fin D → ZMod k,
      ∑ a, (Complex.exp (2 * π * Complex.I / (k : ℂ))) ^ ((e u a : Fin k) : ℕ)
        = ∑ a, (ZMod.toCircle (u a) : ℂ) :=
    fun u => Finset.sum_congr rfl fun a _ => (coe_toCircle_eq_pow (u a)).symm
  have hS' : ∀ ω ∈ S.image e, ε
      ≤ ‖∑ a, (Complex.exp (2 * π * Complex.I / (k : ℂ))) ^ ((ω a : Fin k) : ℕ)‖ := by
    intro ω hω
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hω
    rw [hsum u]
    exact hS u hu
  have hbound := card_le_of_forall_norm_sum_ge hζ hk (S.image e) hε hS'
  rwa [Finset.card_image_of_injective S hinj] at hbound

/-- **The relative cap.**  A set all of whose difference vectors have large character sum is itself
small; translating the set to one of its members reduces this to the absolute cap. -/
theorem card_le_of_forall_norm_relative_toCircle_sum_ge [NeZero k] (hk : 1 < k)
    (S : Finset (Fin D → ZMod k)) {ε : ℝ} (hε : 0 ≤ ε)
    (hS : ∀ u ∈ S, ∀ v ∈ S, ε ≤ ‖∑ a, (ZMod.toCircle (v a - u a) : ℂ)‖) :
    (S.card : ℝ) ≤ 4 * Real.exp (-ε ^ (2 : ℕ) / (4 * (D : ℝ))) * (k : ℝ) ^ D := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hinj : Function.Injective fun v : Fin D → ZMod k => v - u₀ := fun a b hab => by
      simpa using congrArg (fun w => w + u₀) hab
    have hS' : ∀ w ∈ S.image (fun v => v - u₀), ε ≤ ‖∑ a, (ZMod.toCircle (w a) : ℂ)‖ := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      have := hS u₀ hu₀ v hv
      refine le_trans this (le_of_eq ?_)
      exact congrArg _ (Finset.sum_congr rfl fun a _ => rfl)
    have hbound := card_le_of_forall_norm_toCircle_sum_ge hk (S.image (fun v => v - u₀)) hε hS'
    rwa [Finset.card_image_of_injective S hinj] at hbound

/-- The phase vectors a single normalized target captures at radius `delta`. -/
def capturedPhases (k : ℕ) [NeZero k] {D : ℕ} (y : EuclideanSpace ℂ (Fin D)) (δ : ℝ) :
    Finset (Fin D → ZMod k) :=
  letI := Classical.decPred fun m : Fin D → ZMod k =>
    pureStateTraceDistance (torsionRay k m) y ≤ δ
  Finset.univ.filter fun m => pureStateTraceDistance (torsionRay k m) y ≤ δ

theorem mem_capturedPhases [NeZero k] {y : EuclideanSpace ℂ (Fin D)} {δ : ℝ}
    {m : Fin D → ZMod k} :
    m ∈ capturedPhases k y δ ↔ pureStateTraceDistance (torsionRay k m) y ≤ δ := by
  simp only [capturedPhases, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A trace-distance bound is a fidelity bound. -/
theorem one_sub_sq_le_norm_inner_sq {ι : Type*} [Fintype ι] {u y : EuclideanSpace ℂ ι} {δ : ℝ}
    (h : pureStateTraceDistance u y ≤ δ) :
    1 - δ ^ (2 : ℕ) ≤ ‖(inner ℂ y u : ℂ)‖ ^ (2 : ℕ) := by
  have hnn : (0 : ℝ) ≤ δ := le_trans (pureStateTraceDistance_nonneg u y) h
  rw [pureStateTraceDistance] at h
  have h2 : 1 - ‖(inner ℂ u y : ℂ)‖ ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by
    rcases le_or_gt (1 - ‖(inner ℂ u y : ℂ)‖ ^ (2 : ℕ)) 0 with hle | hlt
    · nlinarith
    · have hs := Real.sq_sqrt hlt.le
      nlinarith [Real.sqrt_nonneg (1 - ‖(inner ℂ u y : ℂ)‖ ^ (2 : ℕ))]
  have hconj : ‖(inner ℂ y u : ℂ)‖ = ‖(inner ℂ u y : ℂ)‖ := by
    rw [show (inner ℂ y u : ℂ) = starRingEnd ℂ (inner ℂ u y) from (inner_conj_symm y u).symm,
      RCLike.norm_conj]
  rw [hconj]
  linarith

/-- **The single-target cap.**  A normalized target captures at most `4 e^{-(1-2δ²)²D/4} k^D`
torsion phase vectors. -/
theorem card_capturedPhases_le [NeZero k] (hk : 1 < k) (hD : 0 < D)
    {y : EuclideanSpace ℂ (Fin D)} (hy : ‖y‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : 2 * δ ^ (2 : ℕ) ≤ 1) :
    ((capturedPhases k y δ).card : ℝ)
      ≤ 4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) * (D : ℝ)) ^ (2 : ℕ) / (4 * (D : ℝ))) * (k : ℝ) ^ D := by
  classical
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  refine card_le_of_forall_norm_relative_toCircle_sum_ge hk _ (by nlinarith) ?_
  intro u hu v hv
  have hrel : ∀ a : Fin D, (ZMod.toCircle (v a - u a) : ℂ)
      = (starRingEnd ℂ) (torsionPhaseVec k u a) * torsionPhaseVec k v a := by
    intro a
    rw [AddChar.map_sub_eq_div, Circle.coe_div]
    show (ZMod.toCircle (v a) : ℂ) / (ZMod.toCircle (u a) : ℂ)
        = (starRingEnd ℂ) (ZMod.toCircle (u a) : ℂ) * (ZMod.toCircle (v a) : ℂ)
    rw [div_eq_mul_inv, Complex.inv_eq_conj (Circle.norm_coe _), mul_comm]
  have hmain := norm_sum_relative_phase_ge (q := torsionPhaseVec k u) (r := torsionPhaseVec k v)
    (fun a => norm_torsionPhaseVec _ _) (fun a => norm_torsionPhaseVec _ _) hD hy hδ
    (one_sub_sq_le_norm_inner_sq (mem_capturedPhases.mp hu))
    (one_sub_sq_le_norm_inner_sq (mem_capturedPhases.mp hv))
  rw [show (∑ a, (ZMod.toCircle (v a - u a) : ℂ))
      = ∑ a, (starRingEnd ℂ) (torsionPhaseVec k u a) * torsionPhaseVec k v a from
    Finset.sum_congr rfl fun a _ => hrel a]
  exact hmain

end AnchoredCap

section EasyCap

variable {d k : ℕ}

/-- Every phase vector is its anchored representative shifted by a diagonal phase. -/
theorem eq_cons_anchor_add_diag (m : Fin (d + 1) → ZMod k) :
    m = (Fin.cons 0 (anchorPhaseHom d k m) : Fin (d + 1) → ZMod k) + fun _ => m 0 := by
  funext a
  refine Fin.cases ?_ ?_ a
  · simp only [Pi.add_apply, Fin.cons_zero, zero_add]
  · intro j
    simp only [Pi.add_apply, Fin.cons_succ, anchorPhaseHom_apply, sub_add_cancel]

theorem anchorPhaseHom_cons_add_diag (n : Fin d → ZMod k) (c : ZMod k) :
    anchorPhaseHom d k ((Fin.cons 0 n : Fin (d + 1) → ZMod k) + fun _ => c) = n := by
  funext j
  simp only [anchorPhaseHom_apply, Pi.add_apply, Fin.cons_succ, Fin.cons_zero, zero_add]
  ring

/-- Anchoring is a `k`-to-one fibration. -/
theorem card_fibre_anchorPhaseHom [NeZero k] (n : Fin d → ZMod k) :
    (Finset.univ.filter fun m : Fin (d + 1) → ZMod k => anchorPhaseHom d k m = n).card = k := by
  classical
  have hset : (Finset.univ.filter fun m : Fin (d + 1) → ZMod k => anchorPhaseHom d k m = n)
      = Finset.univ.image
          (fun c : ZMod k => (Fin.cons 0 n : Fin (d + 1) → ZMod k) + fun _ => c) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hm
      refine ⟨m 0, ?_⟩
      rw [← hm]
      exact (eq_cons_anchor_add_diag m).symm
    · rintro ⟨c, rfl⟩
      exact anchorPhaseHom_cons_add_diag n c
  have hinj : Function.Injective
      (fun c : ZMod k => (Fin.cons 0 n : Fin (d + 1) → ZMod k) + fun _ => c) := by
    intro c c' hcc
    have h0 := congrFun hcc 0
    simpa only [Pi.add_apply, Fin.cons_zero, zero_add] using h0
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

/-- **Lemma A, `(7)`, in anchored coordinates.**  The easy projective classes of a dictionary of `N`
normalized targets number at most `4 N e^{-(1-2δ²)²D/4} k^{D-1}`. -/
theorem card_easyAnchored_le [NeZero k] (hk : 1 < k)
    (Y : Finset (EuclideanSpace ℂ (Fin (d + 1)))) (hY : ∀ y ∈ Y, ‖y‖ = 1) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : 2 * δ ^ (2 : ℕ) ≤ 1) :
    (k : ℝ) * ((easyAnchored k Y δ).card : ℝ)
      ≤ (Y.card : ℝ)
        * (4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1)) * (k : ℝ) ^ (d + 1)) := by
  classical
  have hDR : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hcount : (Finset.univ.filter
      fun m : Fin (d + 1) → ZMod k => anchorPhaseHom d k m ∈ easyAnchored k Y δ).card
      = k * (easyAnchored k Y δ).card :=
    card_filter_mem_eq_mul (fun m : Fin (d + 1) → ZMod k => anchorPhaseHom d k m) k
      card_fibre_anchorPhaseHom _
  have hcover : (Finset.univ.filter
      fun m : Fin (d + 1) → ZMod k => anchorPhaseHom d k m ∈ easyAnchored k Y δ)
      ⊆ Y.biUnion (fun y => capturedPhases k y δ) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨y, hy, hle⟩ := mem_easyAnchored.mp hm.2
    refine Finset.mem_biUnion.mpr ⟨y, hy, mem_capturedPhases.mpr ?_⟩
    rw [pureStateTraceDistance_torsionRay_eq_anchored]
    exact hle
  have hexp : -((1 - 2 * δ ^ (2 : ℕ)) * (((d + 1 : ℕ) : ℝ))) ^ (2 : ℕ) / (4 * ((d + 1 : ℕ) : ℝ))
      = -((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1) := by
    push_cast
    field_simp
  have hterm : ∀ y ∈ Y, ((capturedPhases k y δ).card : ℝ)
      ≤ 4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1)) * (k : ℝ) ^ (d + 1) := by
    intro y hy
    have h := card_capturedPhases_le (D := d + 1) hk (Nat.succ_pos d) (hY y hy) hδ hδ2
    rwa [hexp] at h
  have hsum : (((Finset.univ.filter
      fun m : Fin (d + 1) → ZMod k => anchorPhaseHom d k m ∈ easyAnchored k Y δ).card : ℕ) : ℝ)
      ≤ ∑ y ∈ Y, ((capturedPhases k y δ).card : ℝ) := by
    have hle := le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    exact_mod_cast hle
  have hfin : ∑ y ∈ Y, ((capturedPhases k y δ).card : ℝ)
      ≤ (Y.card : ℝ)
        * (4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1)) * (k : ℝ) ^ (d + 1)) := by
    calc ∑ y ∈ Y, ((capturedPhases k y δ).card : ℝ)
        ≤ ∑ _y ∈ Y, 4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1))
            * (k : ℝ) ^ (d + 1) := Finset.sum_le_sum hterm
      _ = (Y.card : ℝ)
            * (4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1))
              * (k : ℝ) ^ (d + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hcount] at hsum
  push_cast at hsum
  linarith

/-- **`(13)` closes the counting hypothesis.**  The card's cap condition makes the easy set a proper
subset of the projective torsion group after removing all `k-1` power preimages. -/
theorem card_easyAnchored_lt_of_cap [NeZero k] (hk : 1 < k)
    (Y : Finset (EuclideanSpace ℂ (Fin (d + 1)))) (hY : ∀ y ∈ Y, ‖y‖ = 1) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : 2 * δ ^ (2 : ℕ) ≤ 1)
    (h13 : 4 * ((k : ℝ) - 1) * (Y.card : ℝ)
      * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) < 1) :
    (k - 1) * (easyAnchored k Y δ).card < k ^ d := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDR : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hcap := card_easyAnchored_le hk Y hY hδ hδ2
  have hmono : Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1))
      ≤ Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg (δ ^ (2 : ℕ)), hDR]
  have hexppos : (0 : ℝ) < Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1)) := Real.exp_pos _
  have hNnn : (0 : ℝ) ≤ (Y.card : ℝ) := Nat.cast_nonneg _
  have hpow : (k : ℝ) ^ (d + 1) = (k : ℝ) * (k : ℝ) ^ d := by ring
  have hpowpos : (0 : ℝ) < (k : ℝ) ^ d := by positivity
  have hXnn : (0 : ℝ) ≤ ((easyAnchored k Y δ).card : ℝ) := Nat.cast_nonneg _
  -- divide the cap by `k`
  have hX : ((easyAnchored k Y δ).card : ℝ)
      ≤ (Y.card : ℝ) * (4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1)))
        * (k : ℝ) ^ d := by
    rw [hpow] at hcap
    nlinarith [hcap, hkR]
  have hreal : ((k : ℝ) - 1) * ((easyAnchored k Y δ).card : ℝ) < (k : ℝ) ^ d := by
    have hstep : ((k : ℝ) - 1) * ((easyAnchored k Y δ).card : ℝ)
        ≤ (4 * ((k : ℝ) - 1) * (Y.card : ℝ)
            * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1))) * (k : ℝ) ^ d := by
      have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      have h1 : ((k : ℝ) - 1) * ((easyAnchored k Y δ).card : ℝ)
          ≤ ((k : ℝ) - 1) * ((Y.card : ℝ)
              * (4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1))) * (k : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hX hk1
      have hc : (0 : ℝ) ≤ 4 * ((k : ℝ) - 1) * (Y.card : ℝ) * (k : ℝ) ^ d :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk1) hNnn) hpowpos.le
      have h2 : ((k : ℝ) - 1) * ((Y.card : ℝ)
            * (4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1))) * (k : ℝ) ^ d)
          ≤ (4 * ((k : ℝ) - 1) * (Y.card : ℝ)
              * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1))) * (k : ℝ) ^ d := by
        calc ((k : ℝ) - 1) * ((Y.card : ℝ)
              * (4 * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1))) * (k : ℝ) ^ d)
            = (4 * ((k : ℝ) - 1) * (Y.card : ℝ) * (k : ℝ) ^ d)
                * Real.exp (-((1 - 2 * δ ^ (2 : ℕ)) ^ (2 : ℕ) / 4) * ((d : ℝ) + 1)) := by ring
          _ ≤ (4 * ((k : ℝ) - 1) * (Y.card : ℝ) * (k : ℝ) ^ d)
                * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hmono hc
          _ = (4 * ((k : ℝ) - 1) * (Y.card : ℝ)
                * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1))) * (k : ℝ) ^ d := by ring
      linarith
    have hlast : (4 * ((k : ℝ) - 1) * (Y.card : ℝ)
        * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1))) * (k : ℝ) ^ d < 1 * (k : ℝ) ^ d :=
      mul_lt_mul_of_pos_right h13 hpowpos
    linarith
  have hcast : (((k - 1) * (easyAnchored k Y δ).card : ℕ) : ℝ)
      = ((k : ℝ) - 1) * ((easyAnchored k Y δ).card : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (le_of_lt hk), Nat.cast_one]
  have : (((k - 1) * (easyAnchored k Y δ).card : ℕ) : ℝ) < ((k ^ d : ℕ) : ℝ) := by
    rw [hcast, Nat.cast_pow]
    exact hreal
  exact_mod_cast this

/-- **Theorem B under the card's cap hypothesis `(13)`.**  No counting hypothesis is left: the
dictionary size, the accuracy and the Hilbert dimension alone decide it. -/
theorem exists_late_recurrence_hard_polygon_of_cap [NeZero k] (hk : k.Prime)
    (E : Fin (d + 1) → ℝ) (hind : LinearIndependent ℚ (projectiveGapPacket E))
    (Y : Finset (EuclideanSpace ℂ (Fin (d + 1)))) (hY : ∀ y ∈ Y, ‖y‖ = 1) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : 2 * δ ^ (2 : ℕ) ≤ 1)
    (h13 : 4 * ((k : ℝ) - 1) * (Y.card : ℝ)
      * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ R : ℝ, A < R ∧
      pureStateTraceDistance (flowRay E R) (flowRay E 0) < ρ ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → ∀ y ∈ Y,
        δ < pureStateTraceDistance (flowRay E ((j : ℝ) * R / (k : ℝ))) y :=
  exists_late_recurrence_rational_slices hk E hind Y hY
    (card_easyAnchored_lt_of_cap hk.one_lt Y hY hδ hδ2 h13) hρ A

end EasyCap

end

end GaloisForLFunctions.HTGeometry
