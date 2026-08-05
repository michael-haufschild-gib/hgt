import GaloisForLFunctions.HTGeometry.DifferentiatedCompanionBox

/-!
# Monotone jet boxes: separation without any bound on the companions

A box in which the distinguished exponent strictly increases while every companion exponent weakly
decreases is separated by the integer order form for *any* nonnegative companion orders.  The
distinguished rate is positive and the companion rates are nonpositive, so the order is a strictly
increasing function of the index: the companions' vanishing pushes the order in the same direction
as the distinguished blow-up, never against it.

Nothing about the companions is bounded, nothing is uniform along the sampled set, and the
companions may be differentiated to arbitrary orders.  The staircase box realizes this for any
number of jets placed on the integer heights of the imaginary axis.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Aligned terms separate a box.**  If every coordinate contributes monotonically to the order
and one contributes strictly, the order form is strictly increasing. -/
theorem strictMono_integerBlowUpOrder_of_alignedTerms {n : ℕ} {κ : Type*} [Preorder κ]
    (d : Fin n → ℤ) (exponent : κ → (Fin n →₀ ℕ)) (k₀ : Fin n)
    (halign : ∀ k, Monotone fun a => ((exponent a k : ℕ) : ℤ) * d k)
    (hstrict : StrictMono fun a => ((exponent a k₀ : ℕ) : ℤ) * d k₀) :
    StrictMono fun a => integerBlowUpOrder d (exponent a) := by
  classical
  intro a b hab
  simp only [integerBlowUpOrder_eq_sum_univ]
  have hsplit : ∀ e : Fin n →₀ ℕ, ∑ k : Fin n, ((e k : ℕ) : ℤ) * d k
      = ((e k₀ : ℕ) : ℤ) * d k₀ + ∑ k ∈ Finset.univ.erase k₀, ((e k : ℕ) : ℤ) * d k := fun e =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ k₀)).symm
  rw [hsplit (exponent a), hsplit (exponent b)]
  exact add_lt_add_of_lt_of_le (hstrict hab)
    (Finset.sum_le_sum fun k _ => halign k hab.le)

/-- **The sign law.**  Split the coordinates into those with nonnegative rate, along which the
exponents rise, and those with nonpositive rate, along which they fall.  Every term is then
monotone, so one strictly increasing distinguished term makes the whole order form strictly
increasing.  No rate is bounded and no exponent is bounded. -/
theorem strictMono_integerBlowUpOrder_of_signed_box {n : ℕ} {κ : Type*} [Preorder κ]
    (d : Fin n → ℤ) (exponent : κ → (Fin n →₀ ℕ)) (P : Fin n → Prop) (k₀ : Fin n)
    (hpos : ∀ k, P k → 0 ≤ d k) (hneg : ∀ k, ¬ P k → d k ≤ 0)
    (hmono : ∀ k, P k → Monotone fun a => exponent a k)
    (hanti : ∀ k, ¬ P k → Antitone fun a => exponent a k)
    (hd₀ : 0 < d k₀) (hstrict : StrictMono fun a => exponent a k₀) :
    StrictMono fun a => integerBlowUpOrder d (exponent a) := by
  refine strictMono_integerBlowUpOrder_of_alignedTerms d exponent k₀ ?_ ?_
  · intro k a b hab
    by_cases hk : P k
    · have h1 : ((exponent a k : ℕ) : ℤ) ≤ ((exponent b k : ℕ) : ℤ) := by
        exact_mod_cast hmono k hk hab
      exact mul_le_mul_of_nonneg_right h1 (hpos k hk)
    · have h1 : ((exponent b k : ℕ) : ℤ) ≤ ((exponent a k : ℕ) : ℤ) := by
        exact_mod_cast hanti k hk hab
      exact mul_le_mul_of_nonpos_right h1 (hneg k hk)
  · intro a b hab
    refine mul_lt_mul_of_pos_right ?_ hd₀
    exact_mod_cast hstrict hab

/-- **Monotone boxes separate themselves.**  With a positive distinguished rate and nonpositive
companion rates, the order form strictly increases along a box whose distinguished exponent
increases and whose companion exponents decrease. -/
theorem strictMono_integerBlowUpOrder_of_monotone_box {n : ℕ} {κ : Type*} [PartialOrder κ]
    (d : Fin n → ℤ) (k₀ : Fin n) (exponent : κ → (Fin n →₀ ℕ))
    (hd₀ : 0 < d k₀) (hdk : ∀ k, k ≠ k₀ → d k ≤ 0)
    (hmono : StrictMono fun a => exponent a k₀)
    (hanti : ∀ k, k ≠ k₀ → Antitone fun a => exponent a k) :
    StrictMono fun a => integerBlowUpOrder d (exponent a) :=
  strictMono_integerBlowUpOrder_of_signed_box d exponent (fun k => k = k₀) k₀
    (fun _ hk => by rw [hk]; exact hd₀.le) (fun k hk => hdk k hk)
    (fun k hk => by rw [hk]; exact hmono.monotone) (fun k hk => hanti k hk) hd₀ hmono

/-- A monotone box is separated by the order form. -/
theorem injective_integerBlowUpOrder_of_monotone_box {n : ℕ} {κ : Type*} [LinearOrder κ]
    (d : Fin n → ℤ) (k₀ : Fin n) (exponent : κ → (Fin n →₀ ℕ))
    (hd₀ : 0 < d k₀) (hdk : ∀ k, k ≠ k₀ → d k ≤ 0)
    (hmono : StrictMono fun a => exponent a k₀)
    (hanti : ∀ k, k ≠ k₀ → Antitone fun a => exponent a k) :
    Function.Injective fun a => integerBlowUpOrder d (exponent a) :=
  (strictMono_integerBlowUpOrder_of_monotone_box d k₀ exponent hd₀ hdk hmono hanti).injective

/-- A signed box is separated by the order form. -/
theorem injective_integerBlowUpOrder_of_signed_box {n : ℕ} {κ : Type*} [LinearOrder κ]
    (d : Fin n → ℤ) (exponent : κ → (Fin n →₀ ℕ)) (P : Fin n → Prop) (k₀ : Fin n)
    (hpos : ∀ k, P k → 0 ≤ d k) (hneg : ∀ k, ¬ P k → d k ≤ 0)
    (hmono : ∀ k, P k → Monotone fun a => exponent a k)
    (hanti : ∀ k, ¬ P k → Antitone fun a => exponent a k)
    (hd₀ : 0 < d k₀) (hstrict : StrictMono fun a => exponent a k₀) :
    Function.Injective fun a => integerBlowUpOrder d (exponent a) :=
  (strictMono_integerBlowUpOrder_of_signed_box d exponent P k₀ hpos hneg hmono hanti
    hd₀ hstrict).injective

/-! ## The staircase box on the integer heights -/

/-- The staircase box: the distinguished exponent climbs from `0` to `N` while every companion
exponent descends from `N` to `0`. -/
noncomputable def staircaseJetBox (n N : ℕ) (a : Fin (N + 1)) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => if k = 0 then (a : ℕ) else N - (a : ℕ))

@[simp] theorem staircaseJetBox_apply (n N : ℕ) (a : Fin (N + 1)) (k : Fin (n + 1)) :
    staircaseJetBox n N a k = if k = 0 then (a : ℕ) else N - (a : ℕ) := by
  simp [staircaseJetBox]

/-- The jets are placed at the integer heights of the imaginary axis. -/
noncomputable def staircaseShift (n : ℕ) : Fin (n + 1) → ℂ :=
  fun k => ((k : ℕ) : ℂ) * Complex.I

@[simp] theorem staircaseShift_im (n : ℕ) (k : Fin (n + 1)) :
    (staircaseShift n k).im = (k : ℕ) := by
  simp [staircaseShift]

@[simp] theorem staircaseShift_zero (n : ℕ) : staircaseShift n 0 = 0 := by
  simp [staircaseShift]

/-! ## Full-rank packets for an arbitrary strictly minimal shift -/

/-- The row nodes admissible for a shift configuration: those keeping every shifted node in the open
upper half-plane. -/
def shiftAdmissibleNodes {n : ℕ} (σ : Fin n → ℂ) : Set ℂ := {w : ℂ | ∀ k, 0 < (w + σ k).im}

/-- A shift with a least imaginary part admits infinitely many row nodes. -/
theorem infinite_shiftAdmissibleNodes {n : ℕ} (σ : Fin n → ℂ) (k₀ : Fin n)
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im ≤ (σ k).im) : (shiftAdmissibleNodes σ).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun p : ℕ => (⟨(p : ℝ), 1 - (σ k₀).im⟩ : ℂ)) ?_ ?_
  · intro p₁ p₂ hp
    have hre : ((p₁ : ℝ)) = ((p₂ : ℝ)) := congrArg Complex.re hp
    exact_mod_cast hre
  · intro p k
    show 0 < (1 - (σ k₀).im) + (σ k).im
    rcases eq_or_ne k k₀ with rfl | hk
    · linarith
    · have := hshift k hk
      linarith

set_option maxHeartbeats 1000000 in
/-- **Full-rank node packets for an arbitrary strictly minimal shift.**  No shift is required to be
real, none is required to be zero, and the companions are differentiated to arbitrary orders and may
vanish anywhere.  The only conditions are on the configuration itself: the distinguished shift has
strictly least imaginary part, and the exponent box is monotone in the distinguished coordinate and
antitone in the companions. -/
theorem exists_row_packet_strictMinimalShift_monotoneBox
    {κ row : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Fintype row] {n q : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (exponent : κ → (Fin n →₀ ℕ))
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im < (σ k).im)
    (hmono : StrictMono fun a => exponent a k₀)
    (hanti : ∀ k, k ≠ k₀ → Antitone fun a => exponent a k)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b k, 0 < (z b + σ k).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + σ p.2))).mulVec := by
  classical
  have hZinj : Function.Injective (fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - σ k₀)) := by
    intro p₁ p₂ hp
    have hcast : ((movingCanonicalZero θ p₁ : ℂ)) = ((movingCanonicalZero θ p₂ : ℂ)) := by
      linear_combination hp
    exact movingCanonicalZero_injective θ (Complex.ofReal_injective hcast)
  have him : ∀ ζ ∈ (Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - σ k₀)),
      ζ.im = -(σ k₀).im := by
    rintro ζ ⟨p, rfl⟩
    simp
  refine exists_row_packet_of_linearIndependent_box (q := q)
    (infinite_shiftAdmissibleNodes σ k₀ fun k hk => (hshift k hk).le)
    (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) exponent ?_ f hf
  refine linearIndependent_restrict_expandedMonomialFamily_of_pointwiseIntegerMultiBlowUp
    (κ := κ) (q := q) (S := shiftAdmissibleNodes σ)
    (Z := Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - σ k₀))
    (exponent := exponent) ?_
  refine pointwiseIntegerMultiBlowUpData_translateJets (κ := κ) (S := shiftAdmissibleNodes σ)
    θ m σ k₀ (fun ζ k => translateJetVanishingOrder θ (m k) (σ k) ζ) exponent
    (Set.infinite_range_of_injective hZinj) ?_ ?_ ?_ ?_ ?_
  · intro ζ hζ y hy k
    show 0 < (ζ + (y : ℂ) * Complex.I + σ k).im
    have h1 : (ζ + (y : ℂ) * Complex.I + σ k).im = ζ.im + y + (σ k).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    rw [h1, him ζ hζ]
    rcases eq_or_ne k k₀ with rfl | hk
    · linarith
    · have := hshift k hk
      linarith
  · rintro ζ ⟨p, rfl⟩
    exact ⟨p, rfl⟩
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
    refine injective_integerBlowUpOrder_of_monotone_box _ k₀ exponent ?_ ?_ hmono hanti
    · have h0 : integerTranslateJetRate m k₀
          (fun k => translateJetVanishingOrder θ (m k) (σ k) ζ) k₀ = (m k₀ : ℤ) + 1 := by
        simp [integerTranslateJetRate]
      rw [h0]
      positivity
    · intro k hk
      have h1 : integerTranslateJetRate m k₀
          (fun k => translateJetVanishingOrder θ (m k) (σ k) ζ) k
            = -((translateJetVanishingOrder θ (m k) (σ k) ζ : ℤ)) := by
        simp [integerTranslateJetRate, hk]
      rw [h1]
      exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- **Unconditional, arbitrarily many differentiated jets.**  For every parameter sequence, number
of companions, tuple of differentiation orders, degree budget and box size there is a node packet in
the open upper half-plane, with pairwise distinct nodes, on which the expanded evaluation map of the
staircase box in the jets `L^{(m k)}(· + k i)` is injective.

Every companion is differentiated and every companion vanishes somewhere upstairs.  The
point-dependent grading reads off each companion's order at each sampled point, and the staircase
shape separates the box whatever those orders are. -/
theorem exists_row_packet_movingCanonicalStaircaseBox
    (θ : BoundedRealSequence) (n q N : ℕ) (m : Fin (n + 1) → ℕ) :
    ∃ z : (Fin (N + 1) × Fin (q + 1)) → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q (n + 1) z (staircaseJetBox n N)
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + staircaseShift n p.2))).mulVec := by
  have hshift : ∀ k : Fin (n + 1), k ≠ 0 →
      (staircaseShift n 0).im < (staircaseShift n k).im := by
    intro k hk
    rw [staircaseShift_im, staircaseShift_im]
    have hk0 : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    have : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
    simp only [Fin.val_zero, Nat.cast_zero]
    exact_mod_cast this
  have hmono : StrictMono fun a : Fin (N + 1) => staircaseJetBox n N a 0 := by
    intro a b hab
    simpa using hab
  have hanti : ∀ k : Fin (n + 1), k ≠ 0 →
      Antitone fun a : Fin (N + 1) => staircaseJetBox n N a k := by
    intro k hk a b hab
    simp only [staircaseJetBox_apply, if_neg hk]
    exact Nat.sub_le_sub_left hab N
  obtain ⟨z, hmem, hinj, hrank⟩ := exists_row_packet_strictMinimalShift_monotoneBox
    (κ := Fin (N + 1)) (row := Fin (N + 1) × Fin (q + 1)) (q := q)
    θ m (staircaseShift n) 0 (staircaseJetBox n N) hshift hmono hanti id Function.injective_id
  refine ⟨z, ?_, hinj, hrank⟩
  intro b
  have hb := hmem b 0
  simpa using hb

end GaloisForLFunctions.HTGeometry
