import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNormalDirectionOfTheDiagonal
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.AFiniteFibreForcesContacts

/-!
# The orbit ring with a base is a tower of lines

No object of finite type carries the contacts of the arithmetic square. This file builds the
object that does, with an exact count of sections, and shows what it is.

The orbits `e_d` span a subring of `𝒢`; with the Teichmüller point `[q]` of a base they generate
the sections `Σ_d e_d·P_d([q])`, `P_d ∈ ℤ[Y]`. At the level `M` only the divisors `d ∣ M` are
used: a polynomial on each of `τ(M)` lines.

* **Components** (`ghostComponent_orbitSection`): on `Γ_n` the section is
  `Σ_{d ∣ gcd(M, n)} d·P_d(qⁿ)`. The graph `Γ_n` sees the lines of the divisors of `gcd(M, n)`.
* **The lines are independent** (`eq_zero_of_orbitSection_eq_zero`): for `q ≥ 2` a section that
  vanishes on every graph has all `P_d = 0`. On the degrees `n = d(1 + Ms)` the gcd is `d`, and a
  polynomial with infinitely many zeros vanishes.
* **The count** (`card_image_orbitLatticeMap`): the sections with `b` digits in `[−A, A]` on each
  line are `((2A + 1)^b)^{τ(M)}`: the count of the toric surface of the base on each line.
* **The contacts** (`span_orbitSection_sub_eq_graphIdeal`): for degrees `m, n ∣ M` the contact of
  `Γ_m` and `Γ_n` on the level `M` is the contact `J(m, n)` of the arithmetic square.
* **One line** (`pow_sub_pow_dvd_orbitSection_sub`): two graphs with the same gcd with `M` are
  not separated by the orbits of the level: every section satisfies `qᵐ − qⁿ ∣ x_m − x_n`, the
  contact of the toric surface.
* **Density** (`exists_orbitSection_eq`): every element of `𝒢` agrees on the first `N` graphs with
  a section of the level `N!`.

* **One ring** (`orbitBaseRing`): the sections of all levels form a subring `𝒪_q` of `𝒢`. Its
  contacts are those of the square for every pair of graphs
  (`span_orbitBaseRing_sub_eq_graphIdeal`); its fibre over every prime is infinite and it is not
  a quotient of a polynomial ring in finitely many variables
  (`infinite_ringHom_orbitBaseRing_zmod`, `not_surjective_mvPolynomial_orbitBaseRing`).
* **The second degree** (`abs_ghostComponent_orbitLatticeMap_le`): on `Γ_n` a section with `b`
  digits in `[−A, A]` on each line is at most `σ(M)·b·A·(q^b)ⁿ`: the restriction multiplies the
  second degree by `n`.
* **The product formula** (`orbitNat_pow_mem`, `ghostComponent_orbitNat_pow`): `e_p^ℓ` lies in
  `𝒪_q`, in the `ℓ`-th power of the ideal of the diagonal, and its value on `Γ_p` is `p^ℓ`. With
  `map_ghostComponent_ker_pow` the forced zeros of order `ℓ` on a graph are attained: Stepanov's
  inequality on `𝒪_q` is the product formula.

So the contacts and a count live on one object, the ring `𝒪_q`, filtered by its levels: `τ(M)`
lines at the level `M`, glued over the primes, each carrying the sections of the toric surface.
The count is that of the toric surface times the number of lines; Riemann–Roch on `𝒪_q` is a
count on each line and gives no inequality between graphs on different lines.
-/

open Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Orbits with a natural index -/

/-- The orbit of length `d`; `0` for `d = 0`. -/
def orbitNat (d : ℕ) : ghostRing := if h : 0 < d then orbit ⟨d, h⟩ else 0

theorem ghostComponent_orbitNat {d : ℕ} (hd : 0 < d) (n : ℕ+) :
    ghostComponent n (orbitNat d) = if d ∣ (n : ℕ) then (d : ℤ) else 0 := by
  rw [orbitNat, dif_pos hd, ghostComponent_apply, orbit_apply]
  rfl

/-! ### Sections of a level -/

/-- A section of the level `M`: the polynomial `P d` on the line of the divisor `d` of `M`,
restricted along `Y = [q]`. -/
def orbitSection (q : ℤ) (M : ℕ) (P : ℕ → ℤ[X]) : ghostRing :=
  ∑ d ∈ M.divisors, orbitNat d * surfaceMap q (P d)

/-- **On `Γ_n` a section of the level `M` is `Σ_{d ∣ gcd(M, n)} d·P_d(qⁿ)`.** -/
theorem ghostComponent_orbitSection (q : ℤ) {M : ℕ} (hM : 0 < M) (P : ℕ → ℤ[X]) (n : ℕ+) :
    ghostComponent n (orbitSection q M P) =
      ∑ d ∈ (Nat.gcd M n).divisors, (d : ℤ) * (P d).eval (q ^ (n : ℕ)) := by
  have hterm : ∀ d ∈ M.divisors, ghostComponent n (orbitNat d * surfaceMap q (P d)) =
      if d ∣ (n : ℕ) then (d : ℤ) * (P d).eval (q ^ (n : ℕ)) else 0 := fun d hd => by
    rw [map_mul, ghostComponent_orbitNat (Nat.pos_of_mem_divisors hd), ghostComponent_surfaceMap]
    split_ifs <;> simp
  rw [orbitSection, map_sum, Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨Nat.dvd_gcd h1 h3, Nat.gcd_ne_zero_left hM.ne'⟩
  · rintro ⟨h1, _⟩
    exact ⟨⟨h1.trans (Nat.gcd_dvd_left _ _), hM.ne'⟩, h1.trans (Nat.gcd_dvd_right _ _)⟩

theorem orbitSection_sub (q : ℤ) (M : ℕ) (P P' : ℕ → ℤ[X]) :
    orbitSection q M (fun d => P d - P' d) = orbitSection q M P - orbitSection q M P' := by
  simp only [orbitSection, map_sub, mul_sub, Finset.sum_sub_distrib]

/-- **The lines are independent.** For a base `q ≥ 2`, a section of the level `M` that vanishes
on every graph vanishes on every line. -/
theorem eq_zero_of_orbitSection_eq_zero {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M)
    {P : ℕ → ℤ[X]} (h : ∀ n : ℕ+, ghostComponent n (orbitSection (q : ℤ) M P) = 0) :
    ∀ d ∈ M.divisors, P d = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have hdM := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    -- on the degrees `d(1 + Ms)` the gcd with `M` is `d`
    have hgcd : ∀ s : ℕ, Nat.gcd M (d * (1 + M * s)) = d := by
      intro s
      obtain ⟨M', rfl⟩ := hdM
      have h1 : Nat.gcd M' (1 + d * M' * s) = 1 := by
        rw [show d * M' * s = M' * (d * s) by ring, Nat.gcd_add_mul_left_right]
        exact Nat.gcd_one_right _
      rw [Nat.gcd_mul_left, h1, mul_one]
    have hroot : ∀ s : ℕ, (P d).eval ((q : ℤ) ^ (d * (1 + M * s))) = 0 := by
      intro s
      have hpos : 0 < d * (1 + M * s) := by positivity
      have hc := h ⟨d * (1 + M * s), hpos⟩
      rw [ghostComponent_orbitSection _ hM, PNat.mk_coe, hgcd s,
        Finset.sum_eq_single_of_mem d (Nat.mem_divisors_self d hd0.ne') (fun d' hd' hne => by
          have hd'd := Nat.dvd_of_mem_divisors hd'
          have hlt : d' < d := lt_of_le_of_ne (Nat.le_of_dvd hd0 hd'd) hne
          rw [ih d' hlt (Nat.mem_divisors.mpr ⟨hd'd.trans hdM, hM.ne'⟩), Polynomial.eval_zero,
            mul_zero])] at hc
      have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
      exact (mul_eq_zero.mp hc).resolve_left hd'
    have hinj : Function.Injective fun s : ℕ => (q : ℤ) ^ (d * (1 + M * s)) := fun s t hst => by
      have hst' : (q : ℤ) ^ (d * (1 + M * s)) = (q : ℤ) ^ (d * (1 + M * t)) := hst
      have h1 : q ^ (d * (1 + M * s)) = q ^ (d * (1 + M * t)) := by exact_mod_cast hst'
      have h2 := Nat.eq_of_mul_eq_mul_left hd0 (Nat.pow_right_injective hq h1)
      exact Nat.eq_of_mul_eq_mul_left hM (by omega)
    refine Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.infinite_range_of_injective hinj).mono ?_)
    rintro _ ⟨s, rfl⟩
    exact hroot s

/-! ### The count -/

/-- The polynomial with the digits `c`. -/
def digitPoly {b : ℕ} (c : Fin b → ℤ) : ℤ[X] := ∑ j : Fin b, C (c j) * X ^ (j : ℕ)

theorem coeff_digitPoly {b : ℕ} (c : Fin b → ℤ) (j : Fin b) : (digitPoly c).coeff j = c j := by
  rw [digitPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro i _ hij
    rw [Polynomial.coeff_C_mul_X_pow, if_neg fun h => hij (Fin.ext h.symm)]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The lattice of sections of the level `M` with `b` digits on each line. -/
def orbitLatticeMap (q : ℤ) (M b : ℕ) (c : ↥M.divisors → Fin b → ℤ) : ghostRing :=
  orbitSection q M fun d => if h : d ∈ M.divisors then digitPoly (c ⟨d, h⟩) else 0

theorem orbitLatticeMap_injective {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M) (b : ℕ) :
    Function.Injective (orbitLatticeMap (q : ℤ) M b) := by
  intro c c' hcc
  have hzero : ∀ n : ℕ+, ghostComponent n (orbitSection (q : ℤ) M fun d =>
      (if h : d ∈ M.divisors then digitPoly (c ⟨d, h⟩) else 0) -
        (if h : d ∈ M.divisors then digitPoly (c' ⟨d, h⟩) else 0)) = 0 := fun n => by
    rw [orbitSection_sub]
    have h := congrArg (ghostComponent n) hcc
    rw [orbitLatticeMap, orbitLatticeMap] at h
    rw [map_sub, h, sub_self]
  have hP := eq_zero_of_orbitSection_eq_zero hq hM hzero
  funext ⟨d, hd⟩ j
  have h := hP d hd
  rw [dif_pos hd, dif_pos hd, sub_eq_zero] at h
  rw [← coeff_digitPoly (c ⟨d, hd⟩) j, ← coeff_digitPoly (c' ⟨d, hd⟩) j, h]

open Classical in
/-- **The count of the level `M`**: `b` digits in `[−A, A]` on each of the `τ(M)` lines. -/
theorem card_image_orbitLatticeMap {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 0 < M) (A b : ℕ) :
    ((Fintype.piFinset fun _ : ↥M.divisors =>
        Fintype.piFinset fun _ : Fin b => Finset.Icc (-(A : ℤ)) A).image
      (orbitLatticeMap (q : ℤ) M b)).card = ((2 * A + 1) ^ b) ^ M.divisors.card := by
  have hcard : (Finset.Icc (-(A : ℤ)) A).card = 2 * A + 1 := by
    rw [Int.card_Icc]
    omega
  rw [Finset.card_image_of_injective _ (orbitLatticeMap_injective hq hM b),
    Fintype.card_piFinset]
  simp [Fintype.card_piFinset, hcard]

/-! ### The contacts -/

theorem orbitSection_single (q : ℤ) {M d : ℕ} (hd : d ∈ M.divisors) :
    orbitSection q M (fun d' => if d' = d then 1 else 0) = orbitNat d := by
  rw [orbitSection, Finset.sum_eq_single_of_mem d hd (fun d' _ hne => by
    rw [if_neg hne, map_zero, mul_zero]), if_pos rfl, map_one, mul_one]

/-- **The level `M` carries the contacts of the arithmetic square** between the graphs of the
degrees dividing `M`. -/
theorem span_orbitSection_sub_eq_graphIdeal (q : ℤ) {M : ℕ} (hM : 0 < M) {m n : ℕ+}
    (hm : (m : ℕ) ∣ M) (hn : (n : ℕ) ∣ M) :
    Ideal.span (Set.range fun P : ℕ → ℤ[X] =>
        ghostComponent m (orbitSection q M P) - ghostComponent n (orbitSection q M P)) =
      graphIdeal m n := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro _ ⟨P, rfl⟩
    exact Ideal.subset_span ⟨orbitSection q M P, rfl⟩
  · rw [graphIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨d, hd, rfl⟩
    have hdM : d ∣ M := by
      rcases hd with ⟨h, _⟩ | ⟨h, _⟩
      · exact h.trans hm
      · exact h.trans hn
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdM hM
    have hmem : ghostComponent m (orbitNat d) - ghostComponent n (orbitNat d) ∈
        Ideal.span (Set.range fun P : ℕ → ℤ[X] =>
          ghostComponent m (orbitSection q M P) - ghostComponent n (orbitSection q M P)) :=
      Ideal.subset_span ⟨fun d' => if d' = d then 1 else 0, by
        show ghostComponent m (orbitSection q M fun d' => if d' = d then 1 else 0) -
          ghostComponent n (orbitSection q M fun d' => if d' = d then 1 else 0) = _
        rw [orbitSection_single q (Nat.mem_divisors.mpr ⟨hdM, hM.ne'⟩)]⟩
    rw [ghostComponent_orbitNat hd0, ghostComponent_orbitNat hd0] at hmem
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, if_neg h2, sub_zero] at hmem
      exact hmem
    · rw [if_neg h2, if_pos h1, zero_sub] at hmem
      exact (Ideal.neg_mem_iff _).mp hmem

/-- **Two graphs with the same gcd with `M` lie on the same lines**: on the level `M` they are
separated only by the base, as on the toric surface. -/
theorem pow_sub_pow_dvd_orbitSection_sub (q : ℤ) {M : ℕ} (hM : 0 < M) {m n : ℕ+}
    (h : Nat.gcd M m = Nat.gcd M n) (P : ℕ → ℤ[X]) :
    q ^ (m : ℕ) - q ^ (n : ℕ) ∣
      ghostComponent m (orbitSection q M P) - ghostComponent n (orbitSection q M P) := by
  rw [ghostComponent_orbitSection q hM, ghostComponent_orbitSection q hM, h,
    ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun d _ => ?_
  rw [← mul_sub]
  exact Dvd.dvd.mul_left (Polynomial.sub_dvd_eval_sub _ _ _) _

/-! ### Density -/

/-- **The tower is dense in the arithmetic square**: every element agrees on the first `N` graphs
with a section of the level `N!`, constant on each line. -/
theorem exists_orbitSection_eq (q : ℤ) (x : ghostRing) (N : ℕ) :
    ∃ P : ℕ → ℤ[X], ∀ n : ℕ+, (n : ℕ) ≤ N →
      ghostComponent n (orbitSection q N.factorial P) = ghostComponent n x := by
  refine ⟨fun d => C (coord x d), fun n hn => ?_⟩
  rw [ghostComponent_orbitSection q (Nat.factorial_pos N),
    Nat.gcd_eq_right (Nat.dvd_factorial n.pos hn), ghostComponent_eq_sum_coord]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Polynomial.eval_C]

/-! ### One ring -/

theorem orbitNat_one : orbitNat 1 = 1 := by
  refine ghostRing_ext fun n => ?_
  rw [ghostComponent_orbitNat one_pos, if_pos (one_dvd _), map_one, Nat.cast_one]

/-- `e_d e_{d'} = gcd(d, d')·e_{lcm(d, d')}` with natural indices. -/
theorem orbitNat_mul_orbitNat {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d') :
    orbitNat d * orbitNat d' = ((Nat.gcd d d' : ℕ) : ℤ) • orbitNat (Nat.lcm d d') := by
  refine ghostRing_ext fun n => ?_
  rw [map_mul, map_zsmul, ghostComponent_orbitNat hd, ghostComponent_orbitNat hd',
    ghostComponent_orbitNat (Nat.lcm_pos hd hd'), smul_eq_mul]
  by_cases h1 : d ∣ (n : ℕ)
  · by_cases h2 : d' ∣ (n : ℕ)
    · rw [if_pos h1, if_pos h2, if_pos (Nat.lcm_dvd h1 h2)]
      exact_mod_cast (Nat.gcd_mul_lcm d d').symm
    · rw [if_pos h1, if_neg h2, if_neg fun h => h2 ((Nat.dvd_lcm_right d d').trans h), mul_zero,
        mul_zero]
  · rw [if_neg h1, if_neg fun h => h1 ((Nat.dvd_lcm_left d d').trans h), zero_mul, mul_zero]

theorem orbitSection_add (q : ℤ) (M : ℕ) (P P' : ℕ → ℤ[X]) :
    orbitSection q M (fun d => P d + P' d) = orbitSection q M P + orbitSection q M P' := by
  simp only [orbitSection, map_add, mul_add, Finset.sum_add_distrib]

theorem orbitSection_neg (q : ℤ) (M : ℕ) (P : ℕ → ℤ[X]) :
    orbitSection q M (fun d => -P d) = -orbitSection q M P := by
  simp only [orbitSection, map_neg, mul_neg, Finset.sum_neg_distrib]

/-- A section of a level is a section of every multiple of the level. -/
theorem orbitSection_of_dvd (q : ℤ) {M L : ℕ} (hML : M ∣ L) (hL : 0 < L) (P : ℕ → ℤ[X]) :
    orbitSection q M P = orbitSection q L (fun d => if d ∣ M then P d else 0) := by
  have hM : M ≠ 0 := (Nat.pos_of_dvd_of_pos hML hL).ne'
  rw [orbitSection, orbitSection, ← Finset.sum_subset (Nat.divisors_subset_of_dvd hL.ne' hML)
    (fun d _ hd => by
      rw [if_neg fun h => hd (Nat.mem_divisors.mpr ⟨h, hM⟩), map_zero, mul_zero])]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [if_pos (Nat.dvd_of_mem_divisors hd)]

theorem orbitSection_single_mul (q : ℤ) {M d : ℕ} (hd : d ∈ M.divisors) (Q : ℤ[X]) :
    orbitSection q M (fun d' => if d' = d then Q else 0) = orbitNat d * surfaceMap q Q := by
  rw [orbitSection, Finset.sum_eq_single_of_mem d hd (fun d' _ hne => by
    rw [if_neg hne, map_zero, mul_zero]), if_pos rfl]

/-- The sections of all levels. -/
def orbitSections (q : ℤ) : Set ghostRing :=
  {x | ∃ M : ℕ, 0 < M ∧ ∃ P : ℕ → ℤ[X], x = orbitSection q M P}

theorem zero_mem_orbitSections (q : ℤ) : (0 : ghostRing) ∈ orbitSections q :=
  ⟨1, one_pos, fun _ => 0, by simp [orbitSection]⟩

theorem add_mem_orbitSections (q : ℤ) {x y : ghostRing} (hx : x ∈ orbitSections q)
    (hy : y ∈ orbitSections q) : x + y ∈ orbitSections q := by
  obtain ⟨M, hM, P, rfl⟩ := hx
  obtain ⟨M', hM', P', rfl⟩ := hy
  refine ⟨M * M', Nat.mul_pos hM hM',
    fun d => (if d ∣ M then P d else 0) + (if d ∣ M' then P' d else 0), ?_⟩
  rw [orbitSection_of_dvd q (Dvd.intro _ rfl) (Nat.mul_pos hM hM') P,
    orbitSection_of_dvd q (Dvd.intro_left _ rfl) (Nat.mul_pos hM hM') P', orbitSection_add]

theorem sum_mem_orbitSections (q : ℤ) {ι : Type*} (s : Finset ι) {g : ι → ghostRing}
    (h : ∀ i ∈ s, g i ∈ orbitSections q) : ∑ i ∈ s, g i ∈ orbitSections q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_orbitSections q
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add_mem_orbitSections q (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem orbitNat_mul_surfaceMap_mem (q : ℤ) {d : ℕ} (hd : 0 < d) (Q : ℤ[X]) :
    orbitNat d * surfaceMap q Q ∈ orbitSections q :=
  ⟨d, hd, fun d' => if d' = d then Q else 0,
    (orbitSection_single_mul q (Nat.mem_divisors_self d hd.ne') Q).symm⟩

/-- **The orbit ring with the base `q`**: the sections of all levels, a subring of the arithmetic
square. -/
def orbitBaseRing (q : ℤ) : Subring ghostRing where
  carrier := orbitSections q
  zero_mem' := zero_mem_orbitSections q
  one_mem' := ⟨1, one_pos, fun _ => 1, by simp [orbitSection, orbitNat_one]⟩
  add_mem' := add_mem_orbitSections q
  neg_mem' := by
    rintro _ ⟨M, hM, P, rfl⟩
    exact ⟨M, hM, fun d => -P d, (orbitSection_neg q M P).symm⟩
  mul_mem' := by
    rintro _ _ ⟨M, hM, P, rfl⟩ ⟨M', hM', P', rfl⟩
    rw [orbitSection, orbitSection, Finset.sum_mul_sum]
    refine sum_mem_orbitSections q _ fun d hd => sum_mem_orbitSections q _ fun d' hd' => ?_
    have hd0 := Nat.pos_of_mem_divisors hd
    have hd0' := Nat.pos_of_mem_divisors hd'
    have hC : surfaceMap q (C ((Nat.gcd d d' : ℕ) : ℤ)) =
        (((Nat.gcd d d' : ℕ) : ℤ) : ghostRing) := by
      simp [surfaceMap]
    have e : orbitNat d * surfaceMap q (P d) * (orbitNat d' * surfaceMap q (P' d')) =
        orbitNat (Nat.lcm d d') *
          surfaceMap q (C ((Nat.gcd d d' : ℕ) : ℤ) * (P d * P' d')) := by
      rw [map_mul, map_mul, hC, mul_mul_mul_comm, orbitNat_mul_orbitNat hd0 hd0', zsmul_eq_mul]
      ring
    rw [e]
    exact orbitNat_mul_surfaceMap_mem q (Nat.lcm_pos hd0 hd0') _

theorem orbitSection_mem_orbitBaseRing (q : ℤ) {M : ℕ} (hM : 0 < M) (P : ℕ → ℤ[X]) :
    orbitSection q M P ∈ orbitBaseRing q := ⟨M, hM, P, rfl⟩

/-- **The orbit ring with a base carries the contacts of the arithmetic square**, for every pair
of graphs. -/
theorem span_orbitBaseRing_sub_eq_graphIdeal (q : ℤ) (m n : ℕ+) :
    Ideal.span {z : ℤ | ∃ x ∈ orbitBaseRing q, z = ghostComponent m x - ghostComponent n x} =
      graphIdeal m n := by
  have hM : 0 < (m : ℕ) * n := Nat.mul_pos m.pos n.pos
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro _ ⟨x, _, rfl⟩
    exact Ideal.subset_span ⟨x, rfl⟩
  · rw [← span_orbitSection_sub_eq_graphIdeal q hM (Dvd.intro _ rfl) (Dvd.intro_left _ rfl)]
    refine Ideal.span_mono ?_
    rintro _ ⟨P, rfl⟩
    exact ⟨orbitSection q ((m : ℕ) * n) P, orbitSection_mem_orbitBaseRing q hM P, rfl⟩

/-- **The fibre of the orbit ring over a prime has infinitely many rational points.** -/
theorem infinite_ringHom_orbitBaseRing_zmod (q : ℤ) {p : ℕ} (hp : p.Prime) :
    Infinite (orbitBaseRing q →+* ZMod p) := by
  refine Infinite.of_injective (fun k : ℕ => reduce p
    ((ghostComponent (Nat.succPNat (p * k))).comp (orbitBaseRing q).subtype)) fun k l hkl => ?_
  by_contra hne
  have hmn : Nat.succPNat (p * k) ≠ Nat.succPNat (p * l) := fun h =>
    hne (Nat.eq_of_mul_eq_mul_left hp.pos (Nat.succPNat_injective h))
  refine graphIdeal_not_le_span_of_not_dvd hmn hp (not_dvd_mul_add_one hp k)
    (not_dvd_mul_add_one hp l) ?_
  rw [← span_orbitBaseRing_sub_eq_graphIdeal q, Ideal.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Ideal.mem_span_singleton.mpr ((reduce_eq_iff p _ _).mp hkl ⟨x, hx⟩)

/-- **The orbit ring with a base is not of finite type.** -/
theorem not_surjective_mvPolynomial_orbitBaseRing (q : ℤ) (k : ℕ)
    (π : MvPolynomial (Fin k) ℤ →+* orbitBaseRing q) : ¬ Function.Surjective π := fun hπ => by
  haveI := finite_ringHom_zmod_of_surjective π hπ 2
  exact not_finite_iff_infinite.mpr (infinite_ringHom_orbitBaseRing_zmod q Nat.prime_two) this

/-! ### The second degree and the product formula -/

theorem abs_eval_digitPoly_le {b A : ℕ} {c : Fin b → ℤ} (hc : ∀ j, |c j| ≤ A) {y : ℤ}
    (hy : 1 ≤ y) : |(digitPoly c).eval y| ≤ b * A * y ^ b := by
  have hy0 : (0 : ℤ) ≤ y := by linarith
  have hterm : ∀ j : Fin b, |c j * y ^ (j : ℕ)| ≤ (A : ℤ) * y ^ b := fun j => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hy0 _)]
    exact mul_le_mul (hc j) (pow_le_pow_right₀ hy j.2.le) (pow_nonneg hy0 _) (Nat.cast_nonneg A)
  have heval : (digitPoly c).eval y = ∑ j : Fin b, c j * y ^ (j : ℕ) := by
    simp [digitPoly, Polynomial.eval_finsetSum]
  rw [heval]
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun j _ => hterm j).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Restriction to `Γ_n` multiplies the second degree by `n`**: a section with `b` digits in
`[−A, A]` on each line of the level `M` is at most `σ(M)·b·A·(q^b)ⁿ` on `Γ_n`. -/
theorem abs_ghostComponent_orbitLatticeMap_le {q : ℕ} (hq : 1 ≤ q) {M : ℕ} (hM : 0 < M)
    {A b : ℕ} {c : ↥M.divisors → Fin b → ℤ} (hc : ∀ d j, |c d j| ≤ A) (n : ℕ+) :
    |ghostComponent n (orbitLatticeMap (q : ℤ) M b c)| ≤
      (∑ d ∈ M.divisors, (d : ℤ)) * (b * A * ((q : ℤ) ^ b) ^ (n : ℕ)) := by
  have hq' : (1 : ℤ) ≤ (q : ℤ) ^ (n : ℕ) := one_le_pow₀ (by exact_mod_cast hq)
  have hsub : (Nat.gcd M n).divisors ⊆ M.divisors :=
    Nat.divisors_subset_of_dvd hM.ne' (Nat.gcd_dvd_left _ _)
  have hpow : ((q : ℤ) ^ b) ^ (n : ℕ) = ((q : ℤ) ^ (n : ℕ)) ^ b := pow_right_comm _ _ _
  rw [orbitLatticeMap, ghostComponent_orbitSection _ hM, Finset.sum_mul, hpow]
  calc |∑ d ∈ (Nat.gcd M n).divisors, (d : ℤ) *
          (if h : d ∈ M.divisors then digitPoly (c ⟨d, h⟩) else 0).eval ((q : ℤ) ^ (n : ℕ))|
      ≤ ∑ d ∈ (Nat.gcd M n).divisors, |(d : ℤ) *
          (if h : d ∈ M.divisors then digitPoly (c ⟨d, h⟩) else 0).eval ((q : ℤ) ^ (n : ℕ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Nat.gcd M n).divisors, (d : ℤ) * (b * A * ((q : ℤ) ^ (n : ℕ)) ^ b) :=
        Finset.sum_le_sum fun d hd => by
          rw [dif_pos (hsub hd), abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (d : ℤ))]
          exact mul_le_mul_of_nonneg_left (abs_eval_digitPoly_le (hc _) hq') (by positivity)
    _ ≤ ∑ d ∈ M.divisors, (d : ℤ) * (b * A * ((q : ℤ) ^ (n : ℕ)) ^ b) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => by positivity

theorem orbitNat_mem_orbitBaseRing (q : ℤ) {d : ℕ} (hd : 0 < d) :
    orbitNat d ∈ orbitBaseRing q := by
  have h := orbitNat_mul_surfaceMap_mem q hd 1
  rwa [map_one, mul_one] at h

/-- `e_p^ℓ` is a section of the orbit ring in the `ℓ`-th power of the ideal of the diagonal. -/
theorem orbitNat_pow_mem (q : ℤ) {p : ℕ} (hp : p.Prime) (l : ℕ) :
    orbitNat p ^ l ∈ orbitBaseRing q ∧
      orbitNat p ^ l ∈ RingHom.ker (ghostComponent 1) ^ l := by
  refine ⟨Subring.pow_mem _ (orbitNat_mem_orbitBaseRing q hp.pos) l, Ideal.pow_mem_pow ?_ l⟩
  rw [RingHom.mem_ker, ghostComponent_orbitNat hp.pos, PNat.one_coe,
    if_neg fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)]

/-- **The forced zeros are attained**: the value of `e_p^ℓ` on `Γ_p` is `p^ℓ`. -/
theorem ghostComponent_orbitNat_pow {p : ℕ} (hp : p.Prime) (l : ℕ) :
    ghostComponent ⟨p, hp.pos⟩ (orbitNat p ^ l) = (p : ℤ) ^ l := by
  rw [map_pow, ghostComponent_orbitNat hp.pos, PNat.mk_coe, if_pos dvd_rfl]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
