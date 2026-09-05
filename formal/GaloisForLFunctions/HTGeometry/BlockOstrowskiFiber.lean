import GaloisForLFunctions.HTGeometry.BlockFiberAmplitude

/-!
# A vanishing fibre amplitude of a several-carrier relation is a polynomial identity

The single-carrier chain turns a vanishing fibre amplitude into the statement that a combination of
symmetrised monomials evaluates to zero at the chosen frequencies.  With several carriers supported
on disjoint blocks the same step goes through, with the blockwise symmetrisation in place of the
symmetrisation: the fibre amplitude of each monomial is the amplitude product times the blockwise
symmetrisation, the amplitude product is common to all monomials and nonzero, so it divides out.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The `Fin M`-indexed blockwise symmetrisation of an order tuple. -/
def slotPermSum {M : ℕ} (blk : Fin M → κ) (s : Fin M → ℕ) : MvPolynomial (Fin M) ℂ :=
  blockPermSum blk fun _ bb => s (bb : Fin M)

/-- The blockwise multiset of an order tuple. -/
def slotCount {M : ℕ} (blk : Fin M → κ) (s : Fin M → ℕ) (k : κ) : ℕ →₀ ℕ :=
  tupleCount fun bb : {l : Fin M // blk l = k} => s (bb : Fin M)

/-- **Blockwise symmetrisations of order tuples with distinct blockwise multisets are linearly
independent.** -/
theorem eq_zero_of_slotPermSum_combination {M : ℕ} (blk : Fin M → κ) {K : Finset (Fin M → ℕ)}
    (c : (Fin M → ℕ) → ℂ)
    (hdistinct : ∀ s ∈ K, ∀ s' ∈ K, (∀ k, slotCount blk s k = slotCount blk s' k) → s = s')
    (h : ∑ s ∈ K, c s • slotPermSum blk s = 0) : ∀ s ∈ K, c s = 0 := by
  classical
  intro s₀ hs₀
  set E : (Fin M → ℕ) → (∀ k : κ, {l : Fin M // blk l = k} → ℕ) :=
    fun s => fun _ bb => s (bb : Fin M) with hE
  have hEinj : Function.Injective E := by
    intro s s' hss
    funext l
    exact congrFun (congrFun hss (blk l)) (⟨l, rfl⟩ : {m : Fin M // blk m = blk l})
  have hinvE : ∀ s : Fin M → ℕ, Function.invFun E (E s) = s :=
    Function.leftInverse_invFun hEinj
  set c' : (∀ k : κ, {l : Fin M // blk l = k} → ℕ) → ℂ :=
    fun S => c (Function.invFun E S) with hc'
  have hsum : ∑ S ∈ K.image E, c' S • blockPermSum blk S = 0 := by
    rw [Finset.sum_image fun s _ s' _ hss => hEinj hss]
    refine Eq.trans (Finset.sum_congr rfl fun s _ => ?_) h
    rw [hc']
    simp only [hinvE s]
    rfl
  have hdistinct' : ∀ S ∈ K.image E, ∀ S' ∈ K.image E,
      (∀ k, tupleCount (S k) = tupleCount (S' k)) → S = S' := by
    intro S hS S' hS' hcount
    rw [Finset.mem_image] at hS hS'
    obtain ⟨s, hs, rfl⟩ := hS
    obtain ⟨s', hs', rfl⟩ := hS'
    exact congrArg E (hdistinct s hs s' hs' hcount)
  have hzero' := eq_zero_of_blockPermSum_combination blk c' hdistinct' hsum (E s₀)
    (Finset.mem_image_of_mem E hs₀)
  rw [hc'] at hzero'
  simp only [hinvE s₀] at hzero'
  exact hzero'

/-! ### From a vanishing fibre amplitude to a polynomial identity -/

/-- **A vanishing fibre amplitude of a several-carrier relation is a polynomial identity.**  Each
monomial contributes its amplitude product times its blockwise symmetrisation; the amplitude product
is common and nonzero, so it divides out. -/
theorem eval_slotPermSum_combination_eq_zero_of_fiber {a : ι → ℂ} {omega : ι → ℝ} {bidx : ι → κ}
    (hom : RationallyIndependentSequence omega) {M : ℕ} {blk : Fin M → κ}
    (hb : ∀ j, ExpSeriesNormallySummable (fun y => if bidx y = blk j then a y else 0) omega)
    {K : Finset (Fin M → ℕ)} (c : (Fin M → ℕ) → ℂ)
    {i : Fin M → ι} (hi : Function.Injective i) (hane : ∀ l, a (i l) ≠ 0)
    (hib : ∀ j, bidx (i j) = blk j)
    (hfibzero : fiberAmplitude
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
        blockMonomialAmplitude (fun j y => if bidx y = blk j then a y else 0) omega
          (c p.1.1) p.1.1 p.2)
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2)
      (tupleFrequency omega i) = 0) :
    MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ))
      (∑ s ∈ K, c s • slotPermSum blk s) = 0 := by
  classical
  set b : Fin M → ι → ℂ := fun j y => if bidx y = blk j then a y else 0 with hbdef
  have hnorm : ∀ s : {s // s ∈ K},
      Summable fun n : Fin M → ι => ‖blockMonomialAmplitude b omega (c s.1) s.1 n‖ :=
    fun s => summable_norm_blockMonomialAmplitude hb (c s.1) s.1
  have hfib := hfibzero
  rw [fiberAmplitude_sigma (J := fun _ : {s // s ∈ K} => (Fin M → ι))
    (fun s : {s // s ∈ K} => blockMonomialAmplitude b omega (c s.1) s.1)
    (fun _ : {s // s ∈ K} => tupleFrequency omega) hnorm] at hfib
  have hterm : ∀ s : {s // s ∈ K},
      fiberAmplitude (blockMonomialAmplitude b omega (c s.1) s.1) (tupleFrequency omega)
          (tupleFrequency omega i)
        = c s.1 * ((∏ l, a (i l)) *
          MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (slotPermSum blk s.1)) := by
    intro s
    rw [show blockMonomialAmplitude b omega (c s.1) s.1
        = fun n : Fin M → ι =>
          c s.1 * ∏ j, b j (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s.1 j from rfl,
      fiberAmplitude_const_mul,
      fiberAmplitude_blockMonomial_eq_blockPermSum hom a bidx blk s.1 hi hib]
    rfl
  rw [Finset.sum_congr rfl fun s _ => hterm s] at hfib
  have hsplit : ∑ s : {s // s ∈ K}, c s.1 * ((∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (slotPermSum blk s.1))
      = (∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ))
          (∑ s ∈ K, c s • slotPermSum blk s) := by
    rw [map_sum, Finset.mul_sum, ← Finset.sum_coe_sort K
      (fun s => (∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (c s • slotPermSum blk s))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval]
    ring
  rw [hsplit] at hfib
  have hprodne : (∏ l, a (i l)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hane l
  exact (mul_eq_zero.mp hfib).resolve_left hprodne

/-- **At the frequency of a blockwise injective tuple, a vanishing relation gives a polynomial
identity.** -/
theorem eval_slotPermSum_combination_eq_zero {a : ι → ℂ} {omega : ι → ℝ} {bidx : ι → κ}
    (hom : RationallyIndependentSequence omega) {M : ℕ} {blk : Fin M → κ}
    (hb : ∀ j, ExpSeriesNormallySummable (fun y => if bidx y = blk j then a y else 0) omega)
    {K : Finset (Fin M → ℕ)} (c : (Fin M → ℕ) → ℂ)
    (hzero : ∀ t : ℝ, ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j)
      (cexpSeriesCarrier (fun y => if bidx y = blk j then a y else 0) omega) (t : ℂ) = 0)
    {i : Fin M → ι} (hi : Function.Injective i) (hane : ∀ l, a (i l) ≠ 0)
    (hib : ∀ j, bidx (i j) = blk j) :
    MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ))
      (∑ s ∈ K, c s • slotPermSum blk s) = 0 := by
  classical
  set b : Fin M → ι → ℂ := fun j y => if bidx y = blk j then a y else 0 with hbdef
  have hnorm : ∀ s : {s // s ∈ K},
      Summable fun n : Fin M → ι => ‖blockMonomialAmplitude b omega (c s.1) s.1 n‖ :=
    fun s => summable_norm_blockMonomialAmplitude hb (c s.1) s.1
  have hvan : ∀ t : ℝ, expSeriesCarrier
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
        blockMonomialAmplitude b omega (c p.1.1) p.1.1 p.2)
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2) t = 0 :=
    fun t => blockExpSeriesCarrier_sigma_eq_zero hb c hzero t
  have hsum : Summable fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
      ‖blockMonomialAmplitude b omega (c p.1.1) p.1.1 p.2‖ :=
    summable_norm_sigma (J := fun _ : {s // s ∈ K} => (Fin M → ι))
      (b := fun s n => blockMonomialAmplitude b omega (c s.1) s.1 n) hnorm
  exact eval_slotPermSum_combination_eq_zero_of_fiber hom hb c hi hane hib
    (fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero _ _ hsum hvan (tupleFrequency omega i))

/-- **Ostrowski for several carriers on disjoint blocks.**  No nonzero finite combination of
differential monomials of a blockwise palette vanishes identically, provided the frequencies are
rationally independent and every block carries infinitely many nonzero amplitudes. -/
theorem eq_zero_of_blockMonomialCombination_vanishing {a : ι → ℂ} {omega : ι → ℝ} {bidx : ι → κ}
    (hom : RationallyIndependentSequence omega) {M : ℕ} {blk : Fin M → κ}
    (hb : ∀ j, ExpSeriesNormallySummable (fun y => if bidx y = blk j then a y else 0) omega)
    (hinf : ∀ k : κ, {y : ι | bidx y = k ∧ a y ≠ 0}.Infinite)
    {K : Finset (Fin M → ℕ)}
    (hdistinct : ∀ s ∈ K, ∀ s' ∈ K, (∀ k, slotCount blk s k = slotCount blk s' k) → s = s')
    (c : (Fin M → ℕ) → ℂ)
    (hzero : ∀ t : ℝ, ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j)
      (cexpSeriesCarrier (fun y => if bidx y = blk j then a y else 0) omega) (t : ℂ) = 0) :
    ∀ s ∈ K, c s = 0 := by
  classical
  have hmapinj : Function.Injective fun y : ι => Complex.I * (omega y : ℂ) := by
    intro y y' hyy
    have hreal : ((omega y : ℝ) : ℂ) = ((omega y' : ℝ) : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero hyy
    exact injective_of_rationallyIndependentSequence hom (by exact_mod_cast hreal)
  set S : Fin M → Set ℂ :=
    fun l => (fun y : ι => Complex.I * (omega y : ℂ)) '' {y : ι | bidx y = blk l ∧ a y ≠ 0}
    with hSdef
  have hSinf : ∀ l, (S l).Infinite := fun l => (hinf (blk l)).image hmapinj.injOn
  have hQ : (∑ s ∈ K, c s • slotPermSum blk s) = 0 := by
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_pi_infinite_injective hSinf _ ?_
    intro x hx hxinj
    have hchoice : ∀ l : Fin M, ∃ y : ι, (bidx y = blk l ∧ a y ≠ 0) ∧
        Complex.I * (omega y : ℂ) = x l := fun l => hx l
    choose i hi0 hival using hchoice
    have hiinj : Function.Injective i := by
      intro l l' hll
      refine hxinj ?_
      rw [← hival l, ← hival l', hll]
    have hkey := eval_slotPermSum_combination_eq_zero hom hb c hzero hiinj
      (fun l => (hi0 l).2) (fun l => (hi0 l).1)
    rwa [show (fun l => Complex.I * (omega (i l) : ℂ)) = x from funext hival] at hkey
  exact eq_zero_of_slotPermSum_combination blk c hdistinct hQ

/-- **The fibre form.**  If every blockwise injective test tuple sees a vanishing fibre amplitude,
the coefficients vanish.  This is the shape a graded argument feeds, one grade at a time. -/
theorem eq_zero_of_blockFiberAmplitudes_vanishing {a : ι → ℂ} {omega : ι → ℝ} {bidx : ι → κ}
    (hom : RationallyIndependentSequence omega) {M : ℕ} {blk : Fin M → κ}
    (hb : ∀ j, ExpSeriesNormallySummable (fun y => if bidx y = blk j then a y else 0) omega)
    (hinf : ∀ k : κ, {y : ι | bidx y = k ∧ a y ≠ 0}.Infinite)
    {K : Finset (Fin M → ℕ)}
    (hdistinct : ∀ s ∈ K, ∀ s' ∈ K, (∀ k, slotCount blk s k = slotCount blk s' k) → s = s')
    (c : (Fin M → ℕ) → ℂ)
    (hfib : ∀ i : Fin M → ι, Function.Injective i → (∀ l, a (i l) ≠ 0) →
      (∀ j, bidx (i j) = blk j) →
      fiberAmplitude
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
          blockMonomialAmplitude (fun j y => if bidx y = blk j then a y else 0) omega
            (c p.1.1) p.1.1 p.2)
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2)
        (tupleFrequency omega i) = 0) :
    ∀ s ∈ K, c s = 0 := by
  classical
  have hmapinj : Function.Injective fun y : ι => Complex.I * (omega y : ℂ) := by
    intro y y' hyy
    have hreal : ((omega y : ℝ) : ℂ) = ((omega y' : ℝ) : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero hyy
    exact injective_of_rationallyIndependentSequence hom (by exact_mod_cast hreal)
  set S : Fin M → Set ℂ :=
    fun l => (fun y : ι => Complex.I * (omega y : ℂ)) '' {y : ι | bidx y = blk l ∧ a y ≠ 0}
    with hSdef
  have hSinf : ∀ l, (S l).Infinite := fun l => (hinf (blk l)).image hmapinj.injOn
  have hQ : (∑ s ∈ K, c s • slotPermSum blk s) = 0 := by
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_pi_infinite_injective hSinf _ ?_
    intro x hx hxinj
    have hchoice : ∀ l : Fin M, ∃ y : ι, (bidx y = blk l ∧ a y ≠ 0) ∧
        Complex.I * (omega y : ℂ) = x l := fun l => hx l
    choose i hi0 hival using hchoice
    have hiinj : Function.Injective i := by
      intro l l' hll
      refine hxinj ?_
      rw [← hival l, ← hival l', hll]
    have hkey := eval_slotPermSum_combination_eq_zero_of_fiber hom hb c hiinj
      (fun l => (hi0 l).2) (fun l => (hi0 l).1)
      (hfib i hiinj (fun l => (hi0 l).2) (fun l => (hi0 l).1))
    rwa [show (fun l => Complex.I * (omega (i l) : ℂ)) = x from funext hival] at hkey
  exact eq_zero_of_slotPermSum_combination blk c hdistinct hQ

end

end GaloisForLFunctions.HTGeometry
