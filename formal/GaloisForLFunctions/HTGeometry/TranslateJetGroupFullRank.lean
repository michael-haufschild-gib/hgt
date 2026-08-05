import GaloisForLFunctions.HTGeometry.MonotoneStaircaseJetBox

/-!
# Several jets at the distinguished shift

The blow-up mechanism singled out one jet: the one whose translate hits a zero of the carrier.  In
fact *every* jet sitting at that same shift blows up there, each at its own rate `m k + 1`, and the
rates are read off from the differentiation orders alone.  What distinguishes a coordinate is
therefore not its index but its shift.

With the rate vector positive on the whole distinguished group and nonpositive off it, the sign law
separates any box whose exponents rise along the group and fall off it.  Arbitrarily many jets may
share the bottom shift.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The integer rate vector for a distinguished shift group: every jet at the distinguished shift
blows up at its own order, every other jet is renormalized by its vanishing order. -/
noncomputable def integerTranslateJetGroupRate {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ)
    (k₀ : Fin n) (V : Fin n → ℕ) : Fin n → ℤ :=
  fun k => if σ k = σ k₀ then ((m k : ℤ) + 1) else -(V k : ℤ)

theorem integerTranslateJetGroupRate_pos {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (V : Fin n → ℕ) {k : Fin n} (hk : σ k = σ k₀) :
    0 < integerTranslateJetGroupRate m σ k₀ V k := by
  rw [integerTranslateJetGroupRate, if_pos hk]
  positivity

theorem integerTranslateJetGroupRate_nonpos {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (V : Fin n → ℕ) {k : Fin n} (hk : σ k ≠ σ k₀) :
    integerTranslateJetGroupRate m σ k₀ V k ≤ 0 := by
  rw [integerTranslateJetGroupRate, if_neg hk]
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

set_option maxHeartbeats 1000000 in
/-- **The blow-up datum with a whole group at the distinguished shift.**  Along the vertical
approach every jet at the distinguished shift blows up at its own order with the factorial leading
value; the remaining jets are renormalized by their vanishing orders. -/
theorem exists_translateJetGroupBlowUp_at {n : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    {S : Set ℂ} {ζ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hS : ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ k, σ k ≠ σ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hV : ∀ k, σ k ≠ σ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V k : ℕ) : ℕ∞)) :
    ∃ (u : ℕ → ℂ) (t : ℕ → ℂ) (c : Fin n → ℂ),
      (∀ j, u j ∈ S) ∧ (∀ j, t j ≠ 0) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
        (∀ k, c k ≠ 0) ∧
        ∀ k, Tendsto (fun j =>
            iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (u j + σ k) *
              t j ^ (integerTranslateJetGroupRate m σ k₀ V k)) atTop (𝓝 (c k)) := by
  classical
  obtain ⟨p, hp⟩ := hzero
  obtain ⟨u, humem, hune, huim, hulim, htlim⟩ := exists_verticalApproach hε hS
  have htne : ∀ j, u j - ζ ≠ 0 := fun j => sub_ne_zero.mpr (hune j)
  have hzeroim : (ζ + σ k₀).im = 0 := by
    rw [hp]
    simp
  have hupper : ∀ j, 0 < (u j + σ k₀).im := by
    intro j
    have h1 : (u j + σ k₀).im = (u j - ζ).im + (ζ + σ k₀).im := by
      simp only [Complex.add_im, Complex.sub_im]
      ring
    rw [h1, hzeroim, add_zero]
    exact huim j
  have hcomp : ∀ k, σ k ≠ σ k₀ → ∃ C : ℂ, C ≠ 0 ∧
      Tendsto (fun j => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (u j + σ k) *
        (u j - ζ) ^ (-(V k : ℤ))) atTop (𝓝 C) :=
    fun k hk => exists_tendsto_zpow_neg_of_analyticOrderAt (hfin k hk) (hV k hk) hulim hune
  refine ⟨u, fun j => u j - ζ,
    fun k => if hk : σ k = σ k₀ then -((-1 : ℂ) ^ (m k) * ((m k).factorial : ℂ))
      else (hcomp k hk).choose,
    humem, htne, hulim, htlim, ?_, ?_⟩
  · intro k
    dsimp only
    by_cases hk : σ k = σ k₀
    · rw [dif_pos hk]
      exact jetLeadingValue_ne_zero _
    · rw [dif_neg hk]
      exact (hcomp k hk).choose_spec.1
  · intro k
    dsimp only
    by_cases hk : σ k = σ k₀
    · rw [dif_pos hk]
      have hrate : integerTranslateJetGroupRate m σ k₀ V k = ((m k + 1 : ℕ) : ℤ) := by
        rw [integerTranslateJetGroupRate, if_pos hk]
        push_cast
        ring
      rw [hrate]
      have hupperk : ∀ j, 0 < (u j + σ k).im := by
        intro j
        rw [hk]
        exact hupper j
      have hlim' : Tendsto u atTop (𝓝 ((movingCanonicalZero θ p : ℂ) - σ k)) := by
        rw [hk, ← hp]
        exact hulim
      have hbase := tendsto_iteratedDeriv_translate_movingCanonicalLogDerivative θ p (m k) (σ k)
        hupperk hlim'
      refine hbase.congr fun j => ?_
      rw [zpow_natCast, hp, hk]
    · rw [dif_neg hk]
      have hrate : integerTranslateJetGroupRate m σ k₀ V k = -(V k : ℤ) := by
        rw [integerTranslateJetGroupRate, if_neg hk]
      rw [hrate]
      exact (hcomp k hk).choose_spec.2

/-- **Point-dependent group blow-up data.**  Each sampled point supplies its own companion orders;
the distinguished group's rates come from the differentiation orders alone. -/
theorem pointwiseIntegerMultiBlowUpData_translateJetGroup {κ : Type*} {n : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : ℂ → Fin n → ℕ)
    {S Z : Set ℂ} {ε : ℝ} (hε : 0 < ε) (exponent : κ → (Fin n →₀ ℕ)) (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hfin : ∀ ζ ∈ Z, ∀ k, σ k ≠ σ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ)
    (hV : ∀ ζ ∈ Z, ∀ k, σ k ≠ σ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V ζ k : ℕ) : ℕ∞))
    (hsep : ∀ ζ ∈ Z, Function.Injective fun a =>
      integerBlowUpOrder (integerTranslateJetGroupRate m σ k₀ (V ζ)) (exponent a)) :
    PointwiseIntegerMultiBlowUpData S
      (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) Z exponent := by
  refine ⟨hZ, fun ζ hζ => ?_⟩
  obtain ⟨u, t, c, humem, htne, hu, ht, hcne, hlim⟩ :=
    exists_translateJetGroupBlowUp_at θ m σ k₀ (V ζ) hε (hS ζ hζ) (hzero ζ hζ) (hfin ζ hζ)
      (hV ζ hζ)
  exact ⟨u, t, c, integerTranslateJetGroupRate m σ k₀ (V ζ),
    humem, htne, hu, ht, hcne, hsep ζ hζ, hlim⟩

set_option maxHeartbeats 1000000 in
/-- **Full-rank node packets in a prescribed sampled set.**  Arbitrarily many jets may sit at the
distinguished shift, each differentiated to its own order; the remaining shifts need only have
strictly larger imaginary part.  The box must rise along the distinguished group and fall off it,
with one coordinate rising strictly.  The nodes are drawn from any infinite set containing an initial
segment of the vertical ray above each sampled zero. -/
theorem exists_row_packet_in_set_minimalShiftGroup_signedBox
    {κ row : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Fintype row] {n q : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (exponent : κ → (Fin n →₀ ℕ)) {S Z : Set ℂ} {ε : ℝ} (hε : 0 < ε)
    (hSinf : S.Infinite) (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hshift : ∀ k, σ k ≠ σ k₀ → (σ k₀).im < (σ k).im)
    (hmono : ∀ k, σ k = σ k₀ → Monotone fun a => exponent a k)
    (hanti : ∀ k, σ k ≠ σ k₀ → Antitone fun a => exponent a k)
    (hstrict : StrictMono fun a => exponent a k₀)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, z b ∈ S) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + σ p.2))).mulVec := by
  classical
  have him : ∀ ζ ∈ Z, ζ.im = -(σ k₀).im := by
    intro ζ hζ
    obtain ⟨p, rfl⟩ := hzero ζ hζ
    simp
  refine exists_row_packet_of_linearIndependent_box (q := q) hSinf
    (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) exponent ?_ f hf
  refine linearIndependent_restrict_expandedMonomialFamily_of_pointwiseIntegerMultiBlowUp
    (κ := κ) (q := q) (S := S) (Z := Z) (exponent := exponent) ?_
  refine pointwiseIntegerMultiBlowUpData_translateJetGroup (κ := κ) (S := S) (Z := Z)
    θ m σ k₀ (fun ζ k => translateJetVanishingOrder θ (m k) (σ k) ζ) hε exponent hZ hS hzero
    ?_ ?_ ?_
  · intro ζ hζ k hk
    refine analyticAt_translate_jet (m k) (σ k) ?_
    have h1 : (ζ + σ k).im = ζ.im + (σ k).im := by simp
    rw [h1, him ζ hζ]
    have := hshift k hk
    linarith
  · intro ζ hζ k hk
    refine analyticOrderAt_translate_jet_eq θ (m k) ?_
    rw [him ζ hζ]
    have := hshift k hk
    linarith
  · intro ζ _
    exact injective_integerBlowUpOrder_of_signed_box _ exponent (fun k => σ k = σ k₀) k₀
      (fun k hk => (integerTranslateJetGroupRate_pos m σ k₀ _ hk).le)
      (fun k hk => integerTranslateJetGroupRate_nonpos m σ k₀ _ hk)
      hmono hanti (integerTranslateJetGroupRate_pos m σ k₀ _ rfl) hstrict

/-- **Full-rank node packets with a whole group at the minimal shift.**  The sampled set is the full
admissible half-plane. -/
theorem exists_row_packet_minimalShiftGroup_signedBox
    {κ row : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Fintype row] {n q : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (exponent : κ → (Fin n →₀ ℕ))
    (hshift : ∀ k, σ k ≠ σ k₀ → (σ k₀).im < (σ k).im)
    (hmono : ∀ k, σ k = σ k₀ → Monotone fun a => exponent a k)
    (hanti : ∀ k, σ k ≠ σ k₀ → Antitone fun a => exponent a k)
    (hstrict : StrictMono fun a => exponent a k₀)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b k, 0 < (z b + σ k).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + σ p.2))).mulVec := by
  classical
  have hle : ∀ k, k ≠ k₀ → (σ k₀).im ≤ (σ k).im := by
    intro k _
    by_cases hk : σ k = σ k₀
    · rw [hk]
    · exact (hshift k hk).le
  have hZinj : Function.Injective (fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - σ k₀)) := by
    intro p₁ p₂ hp
    have hcast : ((movingCanonicalZero θ p₁ : ℂ)) = ((movingCanonicalZero θ p₂ : ℂ)) := by
      linear_combination hp
    exact movingCanonicalZero_injective θ (Complex.ofReal_injective hcast)
  have him : ∀ ζ ∈ (Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - σ k₀)),
      ζ.im = -(σ k₀).im := by
    rintro ζ ⟨p, rfl⟩
    simp
  refine exists_row_packet_in_set_minimalShiftGroup_signedBox (q := q)
    (S := shiftAdmissibleNodes σ)
    (Z := Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - σ k₀)) (ε := 1)
    θ m σ k₀ exponent one_pos (infinite_shiftAdmissibleNodes σ k₀ hle)
    (Set.infinite_range_of_injective hZinj) ?_ ?_ hshift hmono hanti hstrict f hf
  · intro ζ hζ y hy _ k
    show 0 < (ζ + (y : ℂ) * Complex.I + σ k).im
    have h1 : (ζ + (y : ℂ) * Complex.I + σ k).im = ζ.im + y + (σ k).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    rw [h1, him ζ hζ]
    by_cases hk : σ k = σ k₀
    · rw [hk]
      linarith
    · have := hshift k hk
      linarith
  · rintro ζ ⟨p, rfl⟩
    exact ⟨p, rfl⟩

/-! ## A closed instance with an arbitrary height profile -/

/-- Heights of the jets, the distinguished slot pinned to the real axis. -/
def groupStaircaseHeight {n : ℕ} (heights : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ :=
  fun k => if k = 0 then 0 else heights k

@[simp] theorem groupStaircaseHeight_zero {n : ℕ} (heights : Fin (n + 1) → ℕ) :
    groupStaircaseHeight heights 0 = 0 := by
  simp [groupStaircaseHeight]

/-- The jets sit at the prescribed integer heights of the imaginary axis. -/
noncomputable def groupStaircaseShift {n : ℕ} (heights : Fin (n + 1) → ℕ) : Fin (n + 1) → ℂ :=
  fun k => ((groupStaircaseHeight heights k : ℕ) : ℂ) * Complex.I

@[simp] theorem groupStaircaseShift_zero {n : ℕ} (heights : Fin (n + 1) → ℕ) :
    groupStaircaseShift heights 0 = 0 := by
  simp [groupStaircaseShift]

@[simp] theorem groupStaircaseShift_im {n : ℕ} (heights : Fin (n + 1) → ℕ) (k : Fin (n + 1)) :
    (groupStaircaseShift heights k).im = (groupStaircaseHeight heights k : ℕ) := by
  simp [groupStaircaseShift]

theorem groupStaircaseShift_eq_iff {n : ℕ} (heights : Fin (n + 1) → ℕ) (k : Fin (n + 1)) :
    groupStaircaseShift heights k = groupStaircaseShift heights 0 ↔
      groupStaircaseHeight heights k = 0 := by
  rw [groupStaircaseShift_zero, groupStaircaseShift]
  simp [Complex.I_ne_zero]

/-- The box climbs on the ground group and descends on every raised jet. -/
noncomputable def groupStaircaseBox {n : ℕ} (heights : Fin (n + 1) → ℕ) (N : ℕ)
    (a : Fin (N + 1)) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun k => if groupStaircaseHeight heights k = 0 then (a : ℕ) else N - (a : ℕ))

@[simp] theorem groupStaircaseBox_apply {n : ℕ} (heights : Fin (n + 1) → ℕ) (N : ℕ)
    (a : Fin (N + 1)) (k : Fin (n + 1)) :
    groupStaircaseBox heights N a k
      = if groupStaircaseHeight heights k = 0 then (a : ℕ) else N - (a : ℕ) := by
  simp [groupStaircaseBox]

set_option maxHeartbeats 1000000 in
/-- **Unconditional, arbitrarily many jets at arbitrarily many heights.**  For every parameter
sequence, tuple of differentiation orders, tuple of heights, degree budget and box size there is a
node packet in the open upper half-plane, with pairwise distinct nodes, on which the expanded
evaluation map of the group staircase box is injective.

Arbitrarily many jets may share the ground level, each differentiated to its own order; each blows
up at its own rate.  Every raised jet is differentiated too and may vanish at the sampled points to
any order. -/
theorem exists_row_packet_movingCanonicalGroupStaircaseBox
    (θ : BoundedRealSequence) (n q N : ℕ) (m heights : Fin (n + 1) → ℕ) :
    ∃ z : (Fin (N + 1) × Fin (q + 1)) → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q (n + 1) z
        (groupStaircaseBox heights N)
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + groupStaircaseShift heights p.2))).mulVec := by
  have hshift : ∀ k, groupStaircaseShift heights k ≠ groupStaircaseShift heights 0 →
      (groupStaircaseShift heights 0).im < (groupStaircaseShift heights k).im := by
    intro k hk
    have hne : groupStaircaseHeight heights k ≠ 0 := fun h =>
      hk ((groupStaircaseShift_eq_iff heights k).mpr h)
    rw [groupStaircaseShift_im, groupStaircaseShift_im, groupStaircaseHeight_zero]
    have hpos : 0 < groupStaircaseHeight heights k := Nat.pos_of_ne_zero hne
    exact_mod_cast hpos
  have hmono : ∀ k, groupStaircaseShift heights k = groupStaircaseShift heights 0 →
      Monotone fun a : Fin (N + 1) => groupStaircaseBox heights N a k := by
    intro k hk a b hab
    have h0 : groupStaircaseHeight heights k = 0 :=
      (groupStaircaseShift_eq_iff heights k).mp hk
    show groupStaircaseBox heights N a k ≤ groupStaircaseBox heights N b k
    rw [groupStaircaseBox_apply, groupStaircaseBox_apply, if_pos h0, if_pos h0]
    exact hab
  have hanti : ∀ k, groupStaircaseShift heights k ≠ groupStaircaseShift heights 0 →
      Antitone fun a : Fin (N + 1) => groupStaircaseBox heights N a k := by
    intro k hk a b hab
    have hne : groupStaircaseHeight heights k ≠ 0 := fun h =>
      hk ((groupStaircaseShift_eq_iff heights k).mpr h)
    show groupStaircaseBox heights N b k ≤ groupStaircaseBox heights N a k
    rw [groupStaircaseBox_apply, groupStaircaseBox_apply, if_neg hne, if_neg hne]
    exact Nat.sub_le_sub_left hab N
  have hstrict : StrictMono fun a : Fin (N + 1) => groupStaircaseBox heights N a 0 := by
    intro a b hab
    show groupStaircaseBox heights N a 0 < groupStaircaseBox heights N b 0
    rw [groupStaircaseBox_apply, groupStaircaseBox_apply, groupStaircaseHeight_zero,
      if_pos rfl, if_pos rfl]
    exact hab
  obtain ⟨z, hmem, hinj, hrank⟩ := exists_row_packet_minimalShiftGroup_signedBox
    (κ := Fin (N + 1)) (row := Fin (N + 1) × Fin (q + 1)) (q := q)
    θ m (groupStaircaseShift heights) 0 (groupStaircaseBox heights N)
    hshift hmono hanti hstrict id Function.injective_id
  refine ⟨z, ?_, hinj, hrank⟩
  intro b
  have hb := hmem b 0
  simpa using hb

end GaloisForLFunctions.HTGeometry
