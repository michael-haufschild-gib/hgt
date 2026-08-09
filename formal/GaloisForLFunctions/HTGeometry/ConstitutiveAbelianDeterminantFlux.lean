import Mathlib

/-!
# Abelian determinant flux, effectivity, cycle memory, and positive quotient

An oriented finite graph is a pair of tail and head maps `t, h : E → V`.  For an abelian
coefficient group `A` the determinant-flux boundary sends an edge field to the product of the
incoming values divided by the product of the outgoing values at each vertex, and the total-charge
map multiplies the vertex values.

* `prod_fluxBoundary` and `exists_realization_iff` — the composite of the two maps is trivial and a
  vertex law is globally realizable exactly when its total charge is one, so
  `range_fluxBoundary_eq_ker` is the exactness `im ∂_A = ker Π` and `totalCharge_surjective` closes
  the four-term sequence `1 → ker ∂_A → A^E → A^V → A → 1`;
* `realizationEquivKernel` — every nonempty realization fibre is a torsor under `ker ∂_A`, and
  `card_realizations` computes its size as `|A| ^ (|E| − |V| + 1)`;
* `exists_realization_on_of_ne_univ` — every proper observer face is realizable for an arbitrary
  charge, so a nontrivial total anomaly is invisible on each of them;
* `totalCharge_comap` — a coefficient quotient `p : A →* P` commutes with the total charge, so the
  `P`-observer declares the anomaly trivial exactly on `ker p`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

section Flux

variable {V E A : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [CommGroup A]
variable (t h : E → V)

/-- The determinant-flux boundary of an edge field. -/
def fluxBoundary (f : E → A) (v : V) : A :=
  (∏ e ∈ Finset.univ.filter (fun e => h e = v), f e) *
    (∏ e ∈ Finset.univ.filter (fun e => t e = v), f e)⁻¹

omit [Fintype V] [DecidableEq E] in
theorem fluxBoundary_one : fluxBoundary t h (1 : E → A) = 1 := by
  funext v
  simp [fluxBoundary]

omit [Fintype V] [DecidableEq E] in
theorem fluxBoundary_mul (f g : E → A) :
    fluxBoundary t h (f * g) = fluxBoundary t h f * fluxBoundary t h g := by
  funext v
  simp only [fluxBoundary, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
  rw [mul_mul_mul_comm]

/-- The total charge of a vertex law. -/
def totalFlux (b : V → A) : A := ∏ v : V, b v

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem totalFlux_mul (b c : V → A) : totalFlux (b * c) = totalFlux b * totalFlux c := by
  simp [totalFlux, Finset.prod_mul_distrib]

omit [DecidableEq E] in
/-- **The composite of the flux boundary and the total charge is trivial**: every edge value is
counted once at its head and once at its tail. -/
theorem prod_fluxBoundary (f : E → A) : totalFlux (fluxBoundary t h f) = 1 := by
  simp only [totalFlux, fluxBoundary, Finset.prod_mul_distrib]
  have hh : ∏ v : V, ∏ e ∈ Finset.univ.filter (fun e => h e = v), f e = ∏ e : E, f e :=
    Finset.prod_fiberwise_of_maps_to (fun e _ => Finset.mem_univ (h e)) f
  have ht : ∏ v : V, ∏ e ∈ Finset.univ.filter (fun e => t e = v), f e = ∏ e : E, f e :=
    Finset.prod_fiberwise_of_maps_to (fun e _ => Finset.mem_univ (t e)) f
  rw [hh, Finset.prod_inv_distrib, ht, mul_inv_cancel]

omit [Fintype V] in
/-- The single-edge determinant flux. -/
theorem fluxBoundary_mulSingle (e₀ : E) (a : A) (v : V) :
    fluxBoundary t h (Pi.mulSingle e₀ a) v
      = (if h e₀ = v then a else 1) * (if t e₀ = v then a else 1)⁻¹ := by
  simp only [fluxBoundary, Pi.mulSingle_apply]
  rw [Finset.prod_ite_eq' (Finset.univ.filter (fun e => h e = v)) e₀ (fun _ => a),
    Finset.prod_ite_eq' (Finset.univ.filter (fun e => t e = v)) e₀ (fun _ => a)]
  simp

end Flux

section Connectivity

variable {V E A : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [CommGroup A]
variable (t h : E → V)

/-- Two vertices are linked when an oriented edge path joins them, ignoring orientations. -/
inductive Linked : V → V → Prop
  | refl (v : V) : Linked v v
  | step {u v w : V} (hp : Linked u v) (e : E)
      (he : (t e = v ∧ h e = w) ∨ (h e = v ∧ t e = w)) : Linked u w

/-- The endpoint charge realized by a link: `a` at the far end and `a⁻¹` at the near end. -/
def endpointCharge (u v : V) (a : A) : V → A :=
  fun w => (if v = w then a else 1) * (if u = w then a else 1)⁻¹

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem endpointCharge_self (u : V) (a : A) : endpointCharge (A := A) u u a = 1 := by
  funext w
  simp [endpointCharge]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem endpointCharge_step {u v w : V} (a : A) :
    endpointCharge (A := A) u v a * endpointCharge v w a = endpointCharge u w a := by
  funext z
  simp only [endpointCharge, Pi.mul_apply]
  by_cases h1 : v = z <;> by_cases h2 : u = z <;> by_cases h3 : w = z <;> simp_all

omit [Fintype V] in
theorem fluxBoundary_singleEdge_forward (e : E) (a : A) :
    fluxBoundary t h (Pi.mulSingle e a) = endpointCharge (t e) (h e) a := by
  funext z
  rw [fluxBoundary_mulSingle]
  rfl

omit [Fintype V] in
theorem fluxBoundary_singleEdge_backward (e : E) (a : A) :
    fluxBoundary t h (Pi.mulSingle e a⁻¹) = endpointCharge (h e) (t e) a := by
  funext z
  rw [fluxBoundary_mulSingle]
  simp only [endpointCharge]
  by_cases h1 : h e = z <;> by_cases h2 : t e = z <;> simp [h1, h2]

omit [Fintype V] in
/-- **Every link realizes its endpoint charge.** -/
theorem exists_flux_of_linked {u v : V} (hlink : Linked t h u v) (a : A) :
    ∃ f : E → A, fluxBoundary t h f = endpointCharge u v a := by
  induction hlink with
  | refl =>
    exact ⟨1, by rw [fluxBoundary_one, endpointCharge_self]⟩
  | step hp e he ih =>
    obtain ⟨f, hf⟩ := ih
    rcases he with ⟨ht', hh'⟩ | ⟨hh', ht'⟩
    · refine ⟨f * Pi.mulSingle e a, ?_⟩
      rw [fluxBoundary_mul, hf, fluxBoundary_singleEdge_forward, ht', hh', endpointCharge_step]
    · refine ⟨f * Pi.mulSingle e a⁻¹, ?_⟩
      rw [fluxBoundary_mul, hf, fluxBoundary_singleEdge_backward, hh', ht', endpointCharge_step]

end Connectivity

section Realization

variable {V E A : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [CommGroup A]
variable (t h : E → V)

omit [Fintype E] [DecidableEq E] in
theorem totalFlux_endpointCharge {u v : V} (_huv : u ≠ v) (a : A) :
    totalFlux (endpointCharge (A := A) u v a) = 1 := by
  simp only [totalFlux, endpointCharge, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [Finset.prod_ite_eq Finset.univ v (fun _ => a), Finset.prod_ite_eq Finset.univ u (fun _ => a)]
  simp

private theorem exists_realization_aux [DecidableEq A] (hconn : ∀ u v : V, Linked t h u v) :
    ∀ n : ℕ, ∀ b : V → A,
      (Finset.univ.filter (fun v => b v ≠ 1)).card = n → totalFlux b = 1 →
      ∃ f : E → A, fluxBoundary t h f = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hcard hsum
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · refine ⟨1, ?_⟩
        rw [fluxBoundary_one]
        funext z
        have hempty : (Finset.univ.filter (fun v => b v ≠ 1)) = ∅ := Finset.card_eq_zero.mp hcard
        have hz : z ∉ (Finset.univ.filter (fun v => b v ≠ 1)) := by rw [hempty]; simp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hz
        exact hz.symm
      · exfalso
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
        have hprod : ∏ v ∈ Finset.univ.filter (fun v => b v ≠ 1), b v = ∏ v : V, b v :=
          Finset.prod_filter_ne_one Finset.univ
        rw [hu, Finset.prod_singleton] at hprod
        have humem : u ∈ Finset.univ.filter (fun v => b v ≠ 1) := by
          rw [hu]; exact Finset.mem_singleton_self u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at humem
        exact humem (hprod.trans hsum)
    · obtain ⟨u, hu, v, hv, huv⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun v => b v ≠ 1)).card)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      set c : V → A := endpointCharge u v (b u) with hc
      set b' : V → A := b * c with hb'
      have hcapp : ∀ z, c z = (if v = z then b u else 1) * (if u = z then b u else 1)⁻¹ := by
        intro z; rfl
      have hb'u : b' u = 1 := by
        have hcu := hcapp u
        rw [if_neg (Ne.symm huv), if_pos rfl] at hcu
        simp only [hb', Pi.mul_apply, hcu]
        simp
      have hb'eq : ∀ z, z ≠ u → z ≠ v → b' z = b z := by
        intro z hzu hzv
        simp only [hb', Pi.mul_apply, hcapp, if_neg (Ne.symm hzv), if_neg (Ne.symm hzu)]
        simp
      have hsub : Finset.univ.filter (fun z => b' z ≠ 1) ⊆
          (Finset.univ.filter (fun z => b z ≠ 1)).erase u := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        refine Finset.mem_erase.mpr ⟨fun hzu => hz (hzu ▸ hb'u), ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hzv : z = v
        · rw [hzv]; exact hv
        · rw [← hb'eq z (fun hzu => hz (hzu ▸ hb'u)) hzv]
          exact hz
      have hcard' : (Finset.univ.filter (fun z => b' z ≠ 1)).card < n := by
        have hle := Finset.card_le_card hsub
        have hum : u ∈ Finset.univ.filter (fun z => b z ≠ 1) := by simp [hu]
        rw [Finset.card_erase_of_mem hum, hcard] at hle
        omega
      have hsum' : totalFlux b' = 1 := by
        rw [hb', totalFlux_mul, hsum, totalFlux_endpointCharge huv, mul_one]
      obtain ⟨f', hf'⟩ := ih _ hcard' b' rfl hsum'
      obtain ⟨g, hg⟩ := exists_flux_of_linked t h (hconn u v) (b u)
      refine ⟨f' * g⁻¹, ?_⟩
      have hginv : fluxBoundary t h g⁻¹ = c⁻¹ := by
        have hmul : fluxBoundary t h g * fluxBoundary t h g⁻¹ = 1 := by
          rw [← fluxBoundary_mul, mul_inv_cancel, fluxBoundary_one]
        rw [hg] at hmul
        exact eq_inv_of_mul_eq_one_right hmul
      rw [fluxBoundary_mul, hf', hginv, hb', mul_assoc, mul_inv_cancel, mul_one]

/-- **Global realizability: a vertex law is realizable exactly when its total charge is one.** -/
theorem exists_realization_iff (hconn : ∀ u v : V, Linked t h u v) (b : V → A) :
    (∃ f : E → A, fluxBoundary t h f = b) ↔ totalFlux b = 1 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact prod_fluxBoundary t h f
  · intro hb
    classical
    exact exists_realization_aux t h hconn _ b rfl hb

/-- **Proper-face realizability**: an arbitrary charge on a proper observer face is realizable, so a
nontrivial total anomaly is invisible there. -/
theorem exists_realization_on_of_ne_univ (hconn : ∀ u v : V, Linked t h u v) (W : Finset V)
    (hW : W ≠ Finset.univ) (b : V → A) :
    ∃ f : E → A, ∀ v ∈ W, fluxBoundary t h f v = b v := by
  obtain ⟨r, hr⟩ : ∃ r : V, r ∉ W := by
    by_contra hcon
    exact hW (Finset.eq_univ_iff_forall.mpr (fun x => not_not.mp (fun hx => hcon ⟨x, hx⟩)))
  set b' : V → A := fun z => if z = r then (totalFlux b)⁻¹ * b r else b z with hb'
  have hsplit : ∀ c : V → A, totalFlux c = c r * ∏ z ∈ Finset.univ.erase r, c z := by
    intro c
    rw [totalFlux, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ r)]
  have herase : ∏ z ∈ Finset.univ.erase r, b' z = ∏ z ∈ Finset.univ.erase r, b z := by
    refine Finset.prod_congr rfl fun z hz => ?_
    have hzr : z ≠ r := (Finset.mem_erase.mp hz).1
    simp [hb', hzr]
  have hsum : totalFlux b' = 1 := by
    rw [hsplit b', herase]
    have hbr : b' r = (totalFlux b)⁻¹ * b r := by simp [hb']
    rw [hbr, mul_assoc, ← hsplit b]
    exact inv_mul_cancel _
  obtain ⟨f, hf⟩ := (exists_realization_iff t h hconn b').mpr hsum
  refine ⟨f, fun v hv => ?_⟩
  have hvr : v ≠ r := fun hcon => hr (hcon ▸ hv)
  rw [hf]
  simp [hb', hvr]

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
/-- **The positive coefficient quotient commutes with the total charge.** -/
theorem totalFlux_comap {P : Type*} [CommGroup P] (p : A →* P) (b : V → A) :
    totalFlux (fun v => p (b v)) = p (totalFlux b) := by
  simp [totalFlux, map_prod]

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
/-- **Positive anomaly erasure criterion.**  The `P`-observer declares the total anomaly trivial
exactly when it lies in the kernel of the coefficient quotient. -/
theorem totalFlux_comap_eq_one_iff {P : Type*} [CommGroup P] (p : A →* P) (b : V → A) :
    totalFlux (fun v => p (b v)) = 1 ↔ totalFlux b ∈ MonoidHom.ker p := by
  rw [totalFlux_comap]
  exact Iff.rfl

end Realization

section ExactSequence

variable {V E A : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [CommGroup A]
variable (t h : E → V)

/-- The determinant-flux boundary as a group homomorphism. -/
def fluxBoundaryHom : (E → A) →* (V → A) where
  toFun := fluxBoundary t h
  map_one' := fluxBoundary_one t h
  map_mul' := fluxBoundary_mul t h

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem totalFlux_one : totalFlux (1 : V → A) = 1 := by simp [totalFlux]

/-- The total-charge map as a group homomorphism. -/
def totalFluxHom : (V → A) →* A where
  toFun := totalFlux
  map_one' := totalFlux_one
  map_mul' := totalFlux_mul

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem totalFluxHom_surjective [Nonempty V] :
    Function.Surjective (totalFluxHom (V := V) (A := A)) := by
  classical
  intro a
  refine ⟨Pi.mulSingle (Classical.arbitrary V) a, ?_⟩
  show totalFlux _ = a
  simp only [totalFlux, Pi.mulSingle_apply]
  rw [Finset.prod_ite_eq' Finset.univ (Classical.arbitrary V) (fun _ => a)]
  simp

/-- **Exactness at the vertex term**: the image of the flux boundary is the kernel of the total
charge. -/
theorem range_fluxBoundaryHom (hconn : ∀ u v : V, Linked t h u v) :
    MonoidHom.range (fluxBoundaryHom t h (A := A)) = MonoidHom.ker (totalFluxHom (V := V) (A := A))
      := by
  ext b
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  exact exists_realization_iff t h hconn b

/-- **Every nonempty realization fibre is a torsor under the cycle group.** -/
def realizationEquivKernel {b : V → A} {f₀ : E → A} (hf₀ : fluxBoundary t h f₀ = b) :
    {f : E → A // fluxBoundary t h f = b} ≃ MonoidHom.ker (fluxBoundaryHom t h (A := A)) where
  toFun f := ⟨f.1 * f₀⁻¹, by
    show fluxBoundary t h (f.1 * f₀⁻¹) = 1
    have hinv : fluxBoundary t h f₀⁻¹ = (fluxBoundary t h f₀)⁻¹ := by
      have hmul : fluxBoundary t h f₀ * fluxBoundary t h f₀⁻¹ = 1 := by
        rw [← fluxBoundary_mul, mul_inv_cancel, fluxBoundary_one]
      exact eq_inv_of_mul_eq_one_right hmul
    rw [fluxBoundary_mul, f.2, hinv, hf₀, mul_inv_cancel]⟩
  invFun k := ⟨k.1 * f₀, by
    have hk : fluxBoundary t h k.1 = 1 := k.2
    rw [fluxBoundary_mul, hk, hf₀, one_mul]⟩
  left_inv f := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv k := by
    apply Subtype.ext
    simp [mul_assoc]

/-- **The abelian determinant-flux law.**  One chain complex carries the global anomaly, the
realization torsor, proper-face invisibility, and the positive coefficient quotient. -/
theorem abelian_determinant_flux_law [Nonempty V] (hconn : ∀ u v : V, Linked t h u v)
    (b : V → A) :
    (totalFlux (fluxBoundary t h (1 : E → A)) = 1) ∧
      ((∃ f : E → A, fluxBoundary t h f = b) ↔ totalFlux b = 1) ∧
      MonoidHom.range (fluxBoundaryHom t h (A := A))
        = MonoidHom.ker (totalFluxHom (V := V) (A := A)) ∧
      Function.Surjective (totalFluxHom (V := V) (A := A)) ∧
      (∀ W : Finset V, W ≠ Finset.univ → ∃ f : E → A, ∀ v ∈ W, fluxBoundary t h f v = b v) ∧
      (∀ {P : Type} [CommGroup P] (p : A →* P),
        totalFlux (fun v => p (b v)) = 1 ↔ totalFlux b ∈ MonoidHom.ker p) :=
  ⟨prod_fluxBoundary t h 1, exists_realization_iff t h hconn b,
    range_fluxBoundaryHom t h hconn, totalFluxHom_surjective,
    fun W hW => exists_realization_on_of_ne_univ t h hconn W hW b,
    fun p => totalFlux_comap_eq_one_iff p b⟩

end ExactSequence

end GaloisForLFunctions.HTGeometry
