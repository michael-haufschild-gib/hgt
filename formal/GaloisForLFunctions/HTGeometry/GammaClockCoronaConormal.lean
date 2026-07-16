import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The Gamma-clock corona carries exactly one conormal line

The digamma clock source `S h = h(·+1) - h` acts on finite clock packets.  Its dual action on
coefficient streams is `σ = prepend₀ - id`; the adjunction is proved here against the finitely
supported clock pairing, so `σ` is source-defined and not a free construction.

The constraint has no exact conormal carrier: `σ` is injective on raw streams.  Modulo the ideal
of eventually-zero streams — which contains every covector factoring through a finite observation
window — the descended corona constraint acquires a kernel, and that kernel is exactly the line
spanned by the class of the constant stream.  Every finite clock realization therefore kills the
class, the corona realization does not, and the corona quotient is the universal finite-blind
realization: every finite-blind linear realization factors through it uniquely, and every
intertwining realization transports the constant stream into its shadow kernel.

This is the linear-register slice of the corona representability and nontriviality laws for the
Gamma source: a rank-one object fixed by the constraint, invisible to every finite clock, carried
by the corona alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K]

/-- Eventually-zero coefficient streams: the finitely observable covectors. -/
def eventuallyZeroStream : Submodule K (ℕ → K) where
  carrier := {c | ∃ N, ∀ n, N ≤ n → c n = 0}
  add_mem' := by
    rintro a b ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨max M N, fun n hn ↦ ?_⟩
    rw [Pi.add_apply, hM n (le_trans (le_max_left _ _) hn),
      hN n (le_trans (le_max_right _ _) hn), add_zero]
  zero_mem' := ⟨0, fun _ _ ↦ rfl⟩
  smul_mem' := by
    rintro a c ⟨N, hN⟩
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Pi.smul_apply, hN n hn, smul_zero]

/-- The stream corona: coefficient streams modulo finite observability. -/
abbrev StreamCorona := (ℕ → K) ⧸ eventuallyZeroStream K

/-- Prepending a zero coefficient to a stream. -/
def streamPrepend : (ℕ → K) →ₗ[K] (ℕ → K) where
  toFun c n := Nat.casesOn n 0 fun m ↦ c m
  map_add' c d := by
    funext n
    cases n <;> simp
  map_smul' a c := by
    funext n
    cases n <;> simp

@[simp] theorem streamPrepend_apply_zero (c : ℕ → K) :
    streamPrepend K c 0 = 0 := rfl

@[simp] theorem streamPrepend_apply_succ (c : ℕ → K) (m : ℕ) :
    streamPrepend K c (m + 1) = c m := rfl

/-- The dual Gamma-clock constraint on coefficient streams. -/
def streamCoronaSource : (ℕ → K) →ₗ[K] (ℕ → K) :=
  streamPrepend K - LinearMap.id

@[simp] theorem streamCoronaSource_apply_zero (c : ℕ → K) :
    streamCoronaSource K c 0 = -c 0 := by
  simp [streamCoronaSource]

@[simp] theorem streamCoronaSource_apply_succ (c : ℕ → K) (m : ℕ) :
    streamCoronaSource K c (m + 1) = c m - c (m + 1) := by
  simp [streamCoronaSource]

/-- The Gamma clock source `S h = h(·+1) - h` on finite clock packets. -/
def clockPacketSource : (ℕ →₀ K) →ₗ[K] (ℕ →₀ K) :=
  Finsupp.lcomapDomain (fun n ↦ n + 1) (add_left_injective 1) - LinearMap.id

theorem clockPacketSource_single_zero (a : K) :
    clockPacketSource K (Finsupp.single 0 a) = -Finsupp.single 0 a := by
  ext k
  simp [clockPacketSource, Finsupp.lcomapDomain, Finsupp.single_apply]

theorem clockPacketSource_single_succ (m : ℕ) (a : K) :
    clockPacketSource K (Finsupp.single (m + 1) a) =
      Finsupp.single m a - Finsupp.single (m + 1) a := by
  ext k
  simp [clockPacketSource, Finsupp.lcomapDomain, Finsupp.single_apply]

/-- **Source-definedness of the stream constraint.**  Pairing a coefficient stream against the
Gamma-clock source of a finite clock packet is pairing the dual stream constraint against the
packet: `σ` is the exact adjoint of `S`. -/
theorem streamCoronaSource_adjoint (c : ℕ → K) :
    (Finsupp.linearCombination K c).comp (clockPacketSource K) =
      Finsupp.linearCombination K (streamCoronaSource K c) := by
  apply Finsupp.lhom_ext
  intro n a
  cases n with
  | zero =>
      rw [LinearMap.comp_apply, clockPacketSource_single_zero, map_neg,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        streamCoronaSource_apply_zero]
      simp
  | succ m =>
      rw [LinearMap.comp_apply, clockPacketSource_single_succ, map_sub,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, streamCoronaSource_apply_succ]
      simp only [smul_eq_mul]
      ring

/-- **No exact conormal carrier.**  The dual constraint is injective on raw coefficient
streams. -/
theorem streamCoronaSource_injective : Function.Injective (streamCoronaSource K) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  have hzero : streamCoronaSource K c = 0 := LinearMap.mem_ker.mp hc
  funext n
  induction n with
  | zero =>
      have h0 := congrFun hzero 0
      rw [streamCoronaSource_apply_zero] at h0
      simpa [neg_eq_zero] using h0
  | succ m ih =>
      have hs := congrFun hzero (m + 1)
      rw [streamCoronaSource_apply_succ] at hs
      have hstep : c m = c (m + 1) := sub_eq_zero.mp hs
      rw [← hstep]
      exact ih

/-- The finitely observable ideal is stable under the dual constraint. -/
theorem eventuallyZeroStream_le_comap :
    eventuallyZeroStream K ≤
      (eventuallyZeroStream K).comap (streamCoronaSource K) := by
  rintro c ⟨N, hN⟩
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [streamCoronaSource_apply_succ, hN m (by omega), hN (m + 1) (by omega), sub_zero]

/-- The corona-descended Gamma constraint. -/
def streamCoronaConstraint : StreamCorona K →ₗ[K] StreamCorona K :=
  Submodule.mapQ _ _ (streamCoronaSource K) (eventuallyZeroStream_le_comap K)

/-- The constant stream is conormal in the corona: its constraint image is finitely
observable. -/
theorem streamCoronaSource_const_mem :
    streamCoronaSource K (fun _ ↦ (1 : K)) ∈ eventuallyZeroStream K := by
  refine ⟨1, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [streamCoronaSource_apply_succ, sub_self]

/-- The corona class of the constant stream is nonzero: the conormal survives exactly where
finite observation ends. -/
theorem coronaClass_const_ne_zero :
    (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  rintro ⟨N, hN⟩
  exact one_ne_zero (hN N le_rfl)

/-- **The corona conormal is one line.**  The kernel of the corona-descended Gamma constraint is
exactly the span of the class of the constant stream. -/
theorem ker_streamCoronaConstraint :
    LinearMap.ker (streamCoronaConstraint K) =
      Submodule.span K
        {(Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K)} := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hσ : streamCoronaSource K c ∈ eventuallyZeroStream K := by
      have hker := LinearMap.mem_ker.mp hx
      rwa [streamCoronaConstraint, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at hker
    obtain ⟨N, hN⟩ := hσ
    have hconst : ∀ n, N ≤ n → c n = c N := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ m hm ih =>
          have h := hN (m + 1) (by omega)
          rw [streamCoronaSource_apply_succ] at h
          rw [← sub_eq_zero.mp h]
          exact ih
    have hdiff : c - c N • (fun _ ↦ (1 : K)) ∈ eventuallyZeroStream K := by
      refine ⟨N, fun n hn ↦ ?_⟩
      simp [hconst n hn]
    have hmk : (Submodule.Quotient.mk c : StreamCorona K) =
        c N • (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) := by
      rw [← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero]
      exact hdiff
    rw [hmk]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker, streamCoronaConstraint,
      Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    exact streamCoronaSource_const_mem K

/-- Every covector supported in a finite observation window is finitely observable, hence dies in
the corona: finite clock realizations of the conormal class are zero. -/
theorem windowSupported_mem_eventuallyZeroStream (s : Finset ℕ) (c : ℕ → K)
    (hc : ∀ n ∉ s, c n = 0) : c ∈ eventuallyZeroStream K := by
  refine ⟨s.sup id + 1, fun n hn ↦ ?_⟩
  apply hc
  intro hns
  have hle := Finset.le_sup (f := id) hns
  simp only [id] at hle
  omega

theorem coronaClass_eq_zero_of_windowSupported (s : Finset ℕ) (c : ℕ → K)
    (hc : ∀ n ∉ s, c n = 0) :
    (Submodule.Quotient.mk c : StreamCorona K) = 0 :=
  Submodule.Quotient.mk_eq_zero _ |>.mpr
    (windowSupported_mem_eventuallyZeroStream K s c hc)

/-- **Universal finite-blind factorization.**  Every linear realization killing the finitely
observable covectors factors uniquely through the corona quotient. -/
theorem finiteBlind_realization_factors_uniquely
    {W : Type*} [AddCommGroup W] [Module K W]
    (r : (ℕ → K) →ₗ[K] W) (hr : eventuallyZeroStream K ≤ LinearMap.ker r) :
    ∃! rbar : StreamCorona K →ₗ[K] W,
      rbar.comp (eventuallyZeroStream K).mkQ = r := by
  refine ⟨(eventuallyZeroStream K).liftQ r hr,
    (eventuallyZeroStream K).liftQ_mkQ r hr, ?_⟩
  intro g hg
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 := LinearMap.congr_fun hg c
  have h2 := LinearMap.congr_fun ((eventuallyZeroStream K).liftQ_mkQ r hr) c
  exact h1.trans h2.symm

/-- **Conormal transport.**  Every finite-blind realization intertwining the dual constraint with
a shadow sends the constant stream into the shadow kernel: the conormal line is functorial. -/
theorem conormal_transport
    {W : Type*} [AddCommGroup W] [Module K W]
    (r : (ℕ → K) →ₗ[K] W) (τ : W →ₗ[K] W)
    (hr : eventuallyZeroStream K ≤ LinearMap.ker r)
    (hint : r.comp (streamCoronaSource K) = τ.comp r) :
    τ (r (fun _ ↦ (1 : K))) = 0 := by
  have h1 := LinearMap.congr_fun hint (fun _ ↦ (1 : K))
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
  have h2 : r (streamCoronaSource K (fun _ ↦ (1 : K))) = 0 :=
    LinearMap.mem_ker.mp (hr (streamCoronaSource_const_mem K))
  rw [← h1]
  exact h2

/-- **The Gamma corona conormal dichotomy.**  The dual Gamma-clock constraint has no exact
conormal carrier, while its corona descent carries exactly one nonzero conormal line — the class
of the constant stream. -/
theorem gammaClockCorona_conormal_dichotomy :
    Function.Injective (streamCoronaSource K) ∧
      LinearMap.ker (streamCoronaConstraint K) =
        Submodule.span K
          {(Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K)} ∧
      (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) ≠ 0 :=
  ⟨streamCoronaSource_injective K, ker_streamCoronaConstraint K,
    coronaClass_const_ne_zero K⟩

end

end GaloisForLFunctions.HTGeometry
