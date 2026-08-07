import GaloisForLFunctions.HTGeometry.DiscreteOrbitReciprocity
import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivResidue
import GaloisForLFunctions.HTGeometry.TripticCornerAccumulation

/-!
# Triptic orbit-residue reciprocity

Let `τ` and `σ` lie in the upper half plane with `1, τ, σ` independent over the integers, and let
`F` be meromorphic on the plane, `1`-periodic, with constant mixed difference

`F(z+τ+σ) - F(z+τ) - F(z+σ) + F(z) = C`.

The two boundary functions `Δ_σ F` and `Δ_τ F` then have, respectively, `τ`-periodic and
`σ`-periodic principal parts.  Summing a fixed principal-part coefficient of `Δ_σ F` along the
`σ`-orbit of a point gives the same number as summing the corresponding coefficient of `Δ_τ F`
along the `τ`-orbit.

The proof is the direct one: the doubly-indexed coefficient array of `F` has row-independent and
column-independent increments, hence is additively separable; its two boundary jump families have
finite support, so the separated summands are eventually constant in all four directions; and the
two mixed quadrants force the two corner constants to vanish, which is exactly the equality of the
two total jumps.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ### Discrete preliminaries -/

/-- A sequence whose forward increments vanish beyond a threshold is constant beyond it. -/
theorem eq_of_forall_ge_increment_zero {d : ℤ → ℂ} {N : ℤ}
    (h : ∀ n : ℤ, N ≤ n → d (n + 1) = d n) : ∀ n : ℤ, N ≤ n → d n = d N := by
  intro n hn
  induction n, hn using Int.leInduction with
  | base => rfl
  | succ k hk ih => rw [h k hk, ih]

/-- A sequence whose forward increments vanish below a threshold is constant below it. -/
theorem eq_of_forall_le_increment_zero {d : ℤ → ℂ} {N : ℤ}
    (h : ∀ n : ℤ, n < N → d (n + 1) = d n) : ∀ n : ℤ, n ≤ N → d n = d N := by
  intro n hn
  induction n, hn using Int.leInductionDown with
  | base => rfl
  | pred k hk ih =>
      have hstep := h (k - 1) (by omega)
      rw [show k - 1 + 1 = k from by ring] at hstep
      rw [← hstep, ih]

/-- Telescoping over a symmetric integer interval. -/
theorem sum_Ico_increment_telescope (d : ℤ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), (d (n + 1) - d n) = d (N : ℤ) - d (-(N : ℤ)) := by
  classical
  have h := Finset.sum_range_sub (fun j : ℕ => d ((j : ℤ) - (N : ℤ))) (2 * N)
  have hreindex : ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), (d (n + 1) - d n)
      = ∑ j ∈ Finset.range (2 * N),
        ((fun j : ℕ => d ((j : ℤ) - (N : ℤ))) (j + 1)
          - (fun j : ℕ => d ((j : ℤ) - (N : ℤ))) j) := by
    refine Finset.sum_nbij' (i := fun n => (n + (N : ℤ)).toNat)
      (j := fun j => (j : ℤ) - (N : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Ico]
      omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      have h1 : (((n + (N : ℤ)).toNat : ℤ) - (N : ℤ)) = n := by omega
      have h2 : ((((n + (N : ℤ)).toNat + 1 : ℕ) : ℤ) - (N : ℤ)) = n + 1 := by
        push_cast
        omega
      simp only [h1, h2]
  rw [hreindex, h]
  congr 1 <;> [skip; skip] <;> congr 1 <;> push_cast <;> ring

/-- A finitely supported family is supported in a symmetric interval. -/
theorem exists_symmetric_bound_of_finite_support {A : ℤ → ℂ}
    (hA : {n : ℤ | A n ≠ 0}.Finite) :
    ∃ N : ℕ, ∀ n : ℤ, ((N : ℤ) ≤ n ∨ n < -(N : ℤ)) → A n = 0 := by
  classical
  obtain ⟨s, hs⟩ := hA.exists_finset
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ s, n.natAbs < M := by
    refine ⟨(s.image fun n => n.natAbs).sup id + 1, fun n hn => ?_⟩
    have : n.natAbs ≤ (s.image fun n => n.natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hn)
    omega
  refine ⟨M, fun n hn => ?_⟩
  by_contra hne
  have := hM n ((hs n).mpr hne)
  omega


/-! ### The reciprocity theorem -/

section Reciprocity

variable {F : ℂ → ℂ} {τ σ : ℂ}

/-- **Triptic orbit-residue reciprocity.**  For a `1`-periodic meromorphic function with constant
mixed difference, the total order-`ℓ` principal-part mass of `Δ_σ F` along a `σ`-orbit equals the
total order-`ℓ` principal-part mass of `Δ_τ F` along the corresponding `τ`-orbit. -/
theorem triptic_orbit_residue_reciprocity
    (hF : MeromorphicOn F Set.univ)
    (hper : ∀ z : ℂ, F (z + 1) = F z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, F (z + τ + σ) - F (z + τ) - F (z + σ) + F z = Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (p : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) :
    ∑ᶠ m : ℤ, laurentCoeff (fun z => F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ
      = ∑ᶠ n : ℤ, laurentCoeff (fun z => F (z + τ) - F z) (p + (n : ℂ) * τ) ℓ := by
  classical
  set Uτ : ℂ → ℂ := fun z => F (z + σ) - F z with hUτdef
  set Uσ : ℂ → ℂ := fun z => F (z + τ) - F z with hUσdef
  have hUτmero : MeromorphicOn Uτ Set.univ := fun z _ =>
    (meromorphicAt_comp_add.mpr (hF (z + σ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  have hUσmero : MeromorphicOn Uσ Set.univ := fun z _ =>
    (meromorphicAt_comp_add.mpr (hF (z + τ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  -- periodicity of the coefficient functions
  have hFper : ∀ a : ℂ, laurentCoeff F (a + 1) ℓ = laurentCoeff F a ℓ := by
    intro a
    have hfun : (fun z => F (z + 1)) = F := funext hper
    calc laurentCoeff F (a + 1) ℓ
        = laurentCoeff (fun z => F (z + 1)) a ℓ := (laurentCoeff_comp_add F a 1 ℓ).symm
      _ = laurentCoeff F a ℓ := by rw [hfun]
  have hUper1 : ∀ (G : ℂ → ℂ) (h : ℂ), (∀ z : ℂ, F (z + 1) = F z) →
      ∀ a : ℂ, laurentCoeff (fun z => F (z + h) - F z) (a + 1) ℓ
        = laurentCoeff (fun z => F (z + h) - F z) a ℓ := by
    intro G h hp a
    have hfun : (fun z => F (z + 1 + h) - F (z + 1)) = fun z => F (z + h) - F z := by
      funext z
      rw [show z + 1 + h = z + h + 1 from by ring, hp (z + h), hp z]
    calc laurentCoeff (fun z => F (z + h) - F z) (a + 1) ℓ
        = laurentCoeff (fun z => F (z + 1 + h) - F (z + 1)) a ℓ :=
          (laurentCoeff_comp_add (fun z => F (z + h) - F z) a 1 ℓ).symm
      _ = laurentCoeff (fun z => F (z + h) - F z) a ℓ := by rw [hfun]
  have hUτper1 : ∀ a : ℂ, laurentCoeff Uτ (a + 1) ℓ = laurentCoeff Uτ a ℓ :=
    hUper1 Uτ σ hper
  have hUσper1 : ∀ a : ℂ, laurentCoeff Uσ (a + 1) ℓ = laurentCoeff Uσ a ℓ :=
    hUper1 Uσ τ hper
  have hUτperτ : ∀ a : ℂ, laurentCoeff Uτ (a + τ) ℓ = laurentCoeff Uτ a ℓ := by
    intro a
    have hfun : (fun z => Uτ (z + τ)) = fun z => Uτ z + Cst := by
      funext z
      simp only [hUτdef]
      have h := hmixed z
      linear_combination h
    calc laurentCoeff Uτ (a + τ) ℓ
        = laurentCoeff (fun z => Uτ (z + τ)) a ℓ := (laurentCoeff_comp_add Uτ a τ ℓ).symm
      _ = laurentCoeff (fun z => Uτ z + Cst) a ℓ := by rw [hfun]
      _ = laurentCoeff Uτ a ℓ := laurentCoeff_add_const (hUτmero a (Set.mem_univ a)) Cst hℓ
  have hUσperσ : ∀ a : ℂ, laurentCoeff Uσ (a + σ) ℓ = laurentCoeff Uσ a ℓ := by
    intro a
    have hfun : (fun z => Uσ (z + σ)) = fun z => Uσ z + Cst := by
      funext z
      simp only [hUσdef]
      have h := hmixed z
      rw [show z + τ + σ = z + σ + τ from by ring] at h
      linear_combination h
    calc laurentCoeff Uσ (a + σ) ℓ
        = laurentCoeff (fun z => Uσ (z + σ)) a ℓ := (laurentCoeff_comp_add Uσ a σ ℓ).symm
      _ = laurentCoeff (fun z => Uσ z + Cst) a ℓ := by rw [hfun]
      _ = laurentCoeff Uσ a ℓ := laurentCoeff_add_const (hUσmero a (Set.mem_univ a)) Cst hℓ
  -- the coefficient array and its two boundary jump families
  set cc : ℤ → ℤ → ℂ := fun n m => laurentCoeff F (p + (n : ℂ) * τ + (m : ℂ) * σ) ℓ with hccdef
  set B : ℤ → ℂ := fun m => laurentCoeff Uτ (p + (m : ℂ) * σ) ℓ with hBdef
  set A : ℤ → ℂ := fun n => laurentCoeff Uσ (p + (n : ℂ) * τ) ℓ with hAdef
  have hBcol : ∀ n m : ℤ, cc n (m + 1) - cc n m = B m := by
    intro n m
    have hstep : laurentCoeff Uτ (p + (n : ℂ) * τ + (m : ℂ) * σ) ℓ = cc n (m + 1) - cc n m := by
      rw [hUτdef, laurentCoeff_shiftDiff hF σ _ ℓ, hccdef]
      congr 2
      push_cast
      ring
    rw [← hstep, hBdef]
    have hmove : p + (n : ℂ) * τ + (m : ℂ) * σ = (p + (m : ℂ) * σ) + (n : ℂ) * τ := by ring
    rw [hmove, laurentCoeff_add_zsmul_of_period hUτperτ]
  have hArow : ∀ n m : ℤ, cc (n + 1) m - cc n m = A n := by
    intro n m
    have hstep : laurentCoeff Uσ (p + (n : ℂ) * τ + (m : ℂ) * σ) ℓ = cc (n + 1) m - cc n m := by
      rw [hUσdef, laurentCoeff_shiftDiff hF τ _ ℓ, hccdef]
      congr 2
      push_cast
      ring
    rw [← hstep, hAdef]
    have hmove : p + (n : ℂ) * τ + (m : ℂ) * σ = (p + (n : ℂ) * τ) + (m : ℂ) * σ := by ring
    rw [hmove, laurentCoeff_add_zsmul_of_period hUσperσ]
  have hsep : ∀ n m : ℤ, cc n m = cc n 0 + (cc 0 m - cc 0 0) :=
    GaloisForLFunctions.additively_separable_of_indep_increments cc B hBcol
  -- finite supports
  have hindepBA : ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 →
      m = 0 ∧ n = 0 ∧ j = 0 := by
    intro m n j h
    obtain ⟨h1, h2, h3⟩ := hindep n m j (by linear_combination h)
    exact ⟨h2, h1, h3⟩
  have hBfin : {m : ℤ | B m ≠ 0}.Finite :=
    finite_setOf_laurentCoeff_ne_zero_orbit hUτmero hℓ hτ hUτper1 hUτperτ hindepBA p
  have hAfin : {n : ℤ | A n ≠ 0}.Finite :=
    finite_setOf_laurentCoeff_ne_zero_orbit hUσmero hℓ hσ hUσper1 hUσperσ hindep p
  obtain ⟨N₁, hN₁⟩ := exists_symmetric_bound_of_finite_support hAfin
  obtain ⟨N₂, hN₂⟩ := exists_symmetric_bound_of_finite_support hBfin
  set N : ℕ := max N₁ N₂ with hNdef
  have hAvanish : ∀ n : ℤ, ((N : ℤ) ≤ n ∨ n < -(N : ℤ)) → A n = 0 := by
    intro n hn
    refine hN₁ n ?_
    have h1 : (N₁ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_left N₁ N₂
    omega
  have hBvanish : ∀ m : ℤ, ((N : ℤ) ≤ m ∨ m < -(N : ℤ)) → B m = 0 := by
    intro m hm
    refine hN₂ m ?_
    have h1 : (N₂ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_right N₁ N₂
    omega
  -- eventual constancy of the two separated summands
  have haUp : ∀ n : ℤ, (N : ℤ) ≤ n → cc n 0 = cc (N : ℤ) 0 :=
    eq_of_forall_ge_increment_zero (d := fun n => cc n 0) (N := (N : ℤ))
      (fun n hn => by
        have := hArow n 0
        rw [hAvanish n (Or.inl hn)] at this
        linear_combination this)
  have haDown : ∀ n : ℤ, n ≤ -(N : ℤ) → cc n 0 = cc (-(N : ℤ)) 0 :=
    eq_of_forall_le_increment_zero (d := fun n => cc n 0) (N := -(N : ℤ))
      (fun n hn => by
        have := hArow n 0
        rw [hAvanish n (Or.inr hn)] at this
        linear_combination this)
  have hbUp : ∀ m : ℤ, (N : ℤ) ≤ m → cc 0 m = cc 0 (N : ℤ) :=
    eq_of_forall_ge_increment_zero (d := fun m => cc 0 m) (N := (N : ℤ))
      (fun m hm => by
        have := hBcol 0 m
        rw [hBvanish m (Or.inl hm)] at this
        linear_combination this)
  have hbDown : ∀ m : ℤ, m ≤ -(N : ℤ) → cc 0 m = cc 0 (-(N : ℤ)) :=
    eq_of_forall_le_increment_zero (d := fun m => cc 0 m) (N := -(N : ℤ))
      (fun m hm => by
        have := hBcol 0 m
        rw [hBvanish m (Or.inr hm)] at this
        linear_combination this)
  -- the two total jumps
  have hsuppA : Function.support A ⊆ (Finset.Ico (-(N : ℤ)) (N : ℤ) : Finset ℤ) := by
    intro n hn
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hcon
    exact hn (hAvanish n (by omega))
  have hsuppB : Function.support B ⊆ (Finset.Ico (-(N : ℤ)) (N : ℤ) : Finset ℤ) := by
    intro m hm
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hcon
    exact hm (hBvanish m (by omega))
  have hsumA : ∑ᶠ n : ℤ, A n = cc (N : ℤ) 0 - cc (-(N : ℤ)) 0 := by
    rw [finsum_eq_sum_of_support_subset A hsuppA]
    rw [Finset.sum_congr rfl (fun n _ => (hArow n 0).symm)]
    exact sum_Ico_increment_telescope (fun n => cc n 0) N
  have hsumB : ∑ᶠ m : ℤ, B m = cc 0 (N : ℤ) - cc 0 (-(N : ℤ)) := by
    rw [finsum_eq_sum_of_support_subset B hsuppB]
    rw [Finset.sum_congr rfl (fun m _ => (hBcol 0 m).symm)]
    exact sum_Ico_increment_telescope (fun m => cc 0 m) N
  -- the two mixed corners vanish
  have hcorner₁ : cc (N : ℤ) 0 + cc 0 (-(N : ℤ)) - cc 0 0 = 0 := by
    refine laurentCoeff_const_eq_zero_of_mixedQuadrant hF hℓ hFper hτ hσ hindep p
      (ε := 1) (Or.inl rfl) _ N ?_
    intro n m hn hm
    have hval : laurentCoeff F (p + ((1 * n : ℤ) : ℂ) * τ + ((1 * m : ℤ) : ℂ) * σ) ℓ = cc n m := by
      rw [hccdef]
      congr 2 <;> push_cast <;> ring
    rw [hval, hsep n m, haUp n hn, hbDown m hm]
    ring
  have hcorner₂ : cc (-(N : ℤ)) 0 + cc 0 (N : ℤ) - cc 0 0 = 0 := by
    refine laurentCoeff_const_eq_zero_of_mixedQuadrant hF hℓ hFper hτ hσ hindep p
      (ε := -1) (Or.inr rfl) _ N ?_
    intro n m hn hm
    have hval : laurentCoeff F (p + ((-1 * n : ℤ) : ℂ) * τ + ((-1 * m : ℤ) : ℂ) * σ) ℓ
        = cc (-n) (-m) := by
      rw [hccdef]
      congr 2 <;> push_cast <;> ring
    rw [hval, hsep (-n) (-m), haDown (-n) (by omega), hbUp (-m) (by omega)]
    ring
  rw [hsumB, hsumA]
  linear_combination hcorner₂ - hcorner₁


/-- The residue of the logarithmic derivative, read as an integer order. -/
theorem laurentCoeff_logDeriv_eq_untop {Y : ℂ → ℂ} (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (v : ℂ) :
    laurentCoeff (logDeriv Y) v (-1) = (((meromorphicOrderAt Y v).untop₀ : ℤ) : ℂ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfin v)
  have hord : meromorphicOrderAt Y v = (n : ℤ) := hn.symm
  rw [laurentCoeff_logDeriv_eq_order (hY v (Set.mem_univ v)) hord, hord]
  simp

/-- **Multiplicative triptic reciprocity.**  The two orbital divisors of the shift quotients of a
`1`-periodic meromorphic function whose triptic multiplicative cocycle is an exponential character
agree: the total zero/pole order of `Y(·+σ)/Y` along a `σ`-orbit equals the total zero/pole order of
`Y(·+τ)/Y` along the corresponding `τ`-orbit. -/
theorem triptic_multiplicative_divisor_reciprocity
    {Y : ℂ → ℂ} {τ σ : ℂ}
    (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (hYper : ∀ z : ℂ, Y (z + 1) = Y z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, logDeriv Y (z + τ + σ) - logDeriv Y (z + τ)
      - logDeriv Y (z + σ) + logDeriv Y z = Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (p : ℂ) :
    ∑ᶠ m : ℤ, ((((meromorphicOrderAt Y (p + (m : ℂ) * σ + σ)).untop₀
        - (meromorphicOrderAt Y (p + (m : ℂ) * σ)).untop₀ : ℤ) : ℂ))
      = ∑ᶠ n : ℤ, ((((meromorphicOrderAt Y (p + (n : ℂ) * τ + τ)).untop₀
        - (meromorphicOrderAt Y (p + (n : ℂ) * τ)).untop₀ : ℤ) : ℂ)) := by
  have hlogmero : MeromorphicOn (logDeriv Y) Set.univ := fun z _ =>
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  have hper : ∀ z : ℂ, logDeriv Y (z + 1) = logDeriv Y z := by
    intro z
    have hfun : (fun w : ℂ => Y (w + 1)) = Y := funext hYper
    have hd : deriv Y (z + 1) = deriv Y z := by
      have h := deriv_comp_add_const (f := Y) (a := (1 : ℂ)) z
      rw [hfun] at h
      exact h.symm
    rw [logDeriv_apply, logDeriv_apply, hd, hYper z]
  have hrec := triptic_orbit_residue_reciprocity hlogmero hper hmixed hτ hσ hindep p
    (ℓ := (-1 : ℤ)) (by norm_num)
  have hσterm : ∀ m : ℤ,
      laurentCoeff (fun z => logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) (-1)
        = ((((meromorphicOrderAt Y (p + (m : ℂ) * σ + σ)).untop₀
            - (meromorphicOrderAt Y (p + (m : ℂ) * σ)).untop₀ : ℤ) : ℂ)) := by
    intro m
    rw [laurentCoeff_shiftDiff hlogmero σ _ (-1),
      laurentCoeff_logDeriv_eq_untop hY hfin, laurentCoeff_logDeriv_eq_untop hY hfin]
    push_cast
    ring
  have hτterm : ∀ n : ℤ,
      laurentCoeff (fun z => logDeriv Y (z + τ) - logDeriv Y z) (p + (n : ℂ) * τ) (-1)
        = ((((meromorphicOrderAt Y (p + (n : ℂ) * τ + τ)).untop₀
            - (meromorphicOrderAt Y (p + (n : ℂ) * τ)).untop₀ : ℤ) : ℂ)) := by
    intro n
    rw [laurentCoeff_shiftDiff hlogmero τ _ (-1),
      laurentCoeff_logDeriv_eq_untop hY hfin, laurentCoeff_logDeriv_eq_untop hY hfin]
    push_cast
    ring
  rw [← finsum_congr hσterm, ← finsum_congr hτterm]
  exact hrec

end Reciprocity

end GaloisForLFunctions.HTGeometry
