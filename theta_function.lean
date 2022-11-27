import topology.algebra.infinite_sum
import topology.metric_space.basic
import data.complex.exponential
import data.real.pi.bounds
import tactic.omega
import analysis.special_functions.exp
import analysis.special_functions.exp_deriv
import analysis.special_functions.polar_coord
import analysis.special_functions.complex.log
import analysis.special_functions.polynomials
import measure_theory.measure.lebesgue
import measure_theory.integral.integral_eq_improper
import measure_theory.group.measure
import measure_theory.measure.haar_lebesgue
import measure_theory.constructions.prod

noncomputable theory

open classical complex (hiding abs_of_nonneg)
open function measure_theory
open absolute_value filter polynomial metric set

open_locale real

local attribute [instance] prop_decidable
local attribute [instance] type_decidable_eq

def inj_posℤ : ℕ ↪ ℤ := ⟨λ x, (x : ℤ),
  by {intros a b, apply int.coe_nat_inj} ⟩

def inj_negℤ : ℕ ↪ ℤ := ⟨λ x, -(x : ℤ),
begin
  intros a b, simp only [imp_self], intro Hab,
  apply int.coe_nat_inj, apply int.neg_inj,
  exact Hab
end⟩

lemma inj_posℤ_mem_image (x : ℤ)
: x ∈ inj_posℤ.image ⊤ ↔ x ≥ 0 :=
begin
  simp only [set.image_congr, inj_posℤ.equations._eqn_1,
    set.image_univ, set.mem_range, ge_iff_le,
    function.embedding.coe_fn_mk, set.top_eq_univ,
    function.embedding.image_apply],
  split, rintro ⟨y, Hy⟩, rw ←Hy, apply int.coe_nat_nonneg,
  intro Hx, use x.to_nat, rwa int.to_nat_of_nonneg
end

lemma inj_negℤ_mem_image (x : ℤ)
: x ∈ inj_negℤ.image ⊤ ↔ x ≤ 0 :=
begin
  simp only [set.image_congr, set.image_univ,
    set.mem_range, inj_negℤ.equations._eqn_1,
    function.embedding.coe_fn_mk, set.top_eq_univ,
    function.embedding.image_apply],
  split, rintro ⟨y, Hy⟩,
  have : 0 ≤ (y : ℤ),
    by { apply int.coe_nat_nonneg }, linarith,
  intro Hx, use (-x).to_nat,
  have : -x ≥ 0, by linarith,
  rw int.to_nat_of_nonneg, linarith, linarith
end

lemma lattice_1 {T : Type} [semilattice_inf T]
  [order_bot T] {a x : T} (y : T)
  {Hxy : x ≤ y} {Hy : disjoint a y} : disjoint a x :=
begin
  have : (a ⊓ x ≤ a ⊓ y) := by
    { apply inf_le_inf_left, exact Hxy },
  rw disjoint_iff_inf_le at Hy ⊢,
  exact le_trans this Hy
end

namespace finset
noncomputable def inv_map
  {α β : Type} (f : α ↪ β) (s : finset β) : finset α :=
  (s.preimage f) (f.injective.inj_on _)

lemma disjoint_inj' {S T : Type}
  {X : finset S} {Y : finset T} {f : S ↪ T}
: disjoint X (Y.inv_map f) ↔ disjoint (X.map f) Y :=
begin
repeat {rw disjoint_iff},
simp only [eq_empty_iff_forall_not_mem, inf_eq_inter,
  bot_eq_empty, mem_inter, inv_map, mem_preimage,
  mem_map, not_and, forall_exists_index],
split, {
  intros hXY x y y_in_x Hy, have := (hXY y y_in_x),
  rw Hy at this, contradiction
}, {
  intros H x Hx, exact H (f x) x Hx rfl
}
end

@[simp]
lemma inv_map_of_map
  {S T : Type} {X : finset S} {f : S ↪ T}
: inv_map f (map f X) = X :=
begin
  simp only [inv_map], ext,
  simp only [mem_map, mem_preimage],
  split, intro H, obtain ⟨a₁, a₁_in_H, H⟩ := H,
  rw f.injective.eq_iff at H, rw ←H, exact a₁_in_H,
  intro Ha, use a, split, exact Ha, refl
end

lemma disjoint_inj {S T : Type} {X Y : finset S}
  {f : S ↪ T} {hXY : disjoint X Y}
: disjoint (X.map f) (Y.map f) :=
  by { rw [←disjoint_inj', inv_map_of_map], exact hXY }

lemma map_of_inv_map {S T : Type} {X : finset T} {i : S ↪ T}
: (X.inv_map i).map i = {x ∈ X | x ∈ (i.image ⊤)} :=
begin
  ext, simp only [mem_map, sep_def, mem_filter, mem_preimage,
    inv_map, filter_congr_decidable, set.image_univ, set.mem_range,
    set.top_eq_univ, function.embedding.image_apply],
  split, rintro ⟨b, Hb, H⟩,
  rw ←H, split, exact Hb, use b, rintro ⟨Ha, y, Hy⟩,
  use y, rw Hy, split, exact Ha, refl,
end
end finset

section summable_lemmas
open finset

lemma summable_ℤ_imp_subset_summable
  (inj : ℕ ↪ ℤ) (f : ℤ → ℂ) (Hf : summable f)
: summable (λ n : ℕ, f (inj n)) :=
begin
  rw summable_iff_vanishing at Hf ⊢ , intros e He,
  replace Hf := Hf e He, obtain ⟨S⟩ := Hf,
  let i_inv_S := S.inv_map inj,
  use i_inv_S, intros t Ht, rw [←sum_map],
  apply Hf_h, rw ←disjoint_inj', exact Ht
end

lemma not_mem_imp_neq {S T : Type} [has_mem S T]
  {a : S} {X : T} (Ha : a ∉ X)
: ∀ (b : S), b ∈ X → b ≠ a :=
  by { intros b Hb Hab, rw Hab at Hb, exact Ha Hb }

lemma add_abs_bound {x y : ℂ} {a b : ℝ}
  (Hx : abs x < a) (Hy : abs y < b)
: abs (x + y) < a + b := by
{ have : abs (x + y) ≤ abs x + abs y,
    by apply absolute_value.add_le, linarith }

lemma summable_ℤ_if_summable_two_sides
  (f : ℤ → ℂ) (Hpos : summable (λ n : ℕ, f n))
  (Hneg : summable (λ n : ℕ, f (-n))) : summable f :=
begin
  rw summable_iff_vanishing, intros e He,
  rw [metric.mem_nhds_iff] at He,
  obtain ⟨ε, Hε, He⟩ := He,
  obtain ⟨s₁, Hs₁⟩ :=
    (iff.mp summable_iff_vanishing Hpos) (ball 0 (ε/2))
    (by {apply ball_mem_nhds, linarith}),
  obtain ⟨s₂, Hs₂⟩ :=
    (iff.mp summable_iff_vanishing Hneg) (ball 0 (ε/2))
    (by {apply ball_mem_nhds, linarith}),
  clear Hpos Hneg,
  use (s₁.map inj_posℤ) ∪ (s₂.map inj_negℤ) ∪ {0},
  intros t Ht, apply He, clear He, clear e,
  repeat {rw finset.disjoint_union_right at Ht},
  rcases Ht with ⟨⟨Ht₁, Ht₂⟩, t_ne_0⟩,
  rw finset.disjoint_singleton_right at t_ne_0,
  replace t_ne_0 := not_mem_imp_neq t_ne_0,
  rw [disjoint.comm, ←disjoint_inj', disjoint.comm] at Ht₁ Ht₂,
  replace Hs₁ := Hs₁ (t.inv_map inj_posℤ) Ht₁,
  replace Hs₂ := Hs₂ (t.inv_map inj_negℤ) Ht₂,
  clear Ht₁ Ht₂,
  simp only [
    show (λ (b : ℕ), f ↑b) = λ (b : ℕ), f (inj_posℤ b), by {ext1, congr},
    show (λ (b : ℕ), f (-↑b)) = λ (b : ℕ), f (inj_negℤ b), by {ext1, congr},
    ←sum_map, map_of_inv_map,
    inj_posℤ_mem_image, inj_negℤ_mem_image]
  at Hs₁ Hs₂,
  have : t = {x ∈ t | x ≤ 0} ∪ {x ∈ t | x ≥ 0} :=
  begin
    ext, simp only [finset.mem_union, finset.sep_def,
      finset.mem_filter, ←and_or_distrib_left, iff_self_and],
    intro Ha, have := t_ne_0 a Ha, omega
  end,
  rw [this, sum_union], clear this,
  {
    simp only [ball, set.mem_set_of_eq,
      dist_zero_right, complex.norm_eq_abs] at Hs₁ Hs₂ ⊢,
    rw [show ε = ε / 2 + ε / 2, by linarith],
    apply add_abs_bound, repeat {assumption}
  }, {
    clear this, rw disjoint_iff,
    simp only [finset.inf_eq_inter,
      finset.bot_eq_empty, finset.sep_def,
      finset.eq_empty_iff_forall_not_mem,
      not_and, finset.mem_inter, finset.mem_filter],
    rintro x ⟨H1, H2⟩ H3, have := t_ne_0 x H1, omega
  }
end
end summable_lemmas

lemma real_bounded_iff_subset_Icc {X : set ℝ}
: bounded X ↔ ∃ (M N : ℝ), X ⊆ (set.Icc M N) :=
begin
  simp only [real.bounded_iff_bdd_below_bdd_above,
    bdd_below_def, bdd_above_def, set.mem_set_of_eq],
  split, {
    rintro ⟨⟨M, H1⟩, ⟨N, H2⟩⟩, use M, use N,
    change ∀x ∈ X, M ≤ x ∧ x ≤ N,
    intros x Hx, split, exact H1 x Hx, exact H2 x Hx
  }, {
    rintro ⟨M, N, H⟩, split,
    use M, intros y Hy, exact (H Hy).1,
    use N, intros y Hy, exact (H Hy).2,
  }
end

lemma bounded_if_tends_neginf {f : ℝ → ℝ}
(Hpos : tendsto f at_top at_top)
(Hneg : tendsto f at_bot at_top)
: bounded {x : ℝ | f x < 0} :=
begin
  replace Hneg := (Hneg $ Ioi_mem_at_top 0),
  replace Hpos := (Hpos $ Ioi_mem_at_top 0),
  simp only [filter.mem_at_top_sets,
    filter.mem_map, filter.mem_at_bot_sets,
    set.mem_preimage, set.mem_Ioi] at *,
  cases Hneg with M Hneg,
  cases Hpos with N Hpos,
  simp only [real_bounded_iff_subset_Icc],
  use M, use N, intro x,
  simp_rw [set.mem_set_of_eq], intro Hx,
  have H1 := Hneg x, have H2 := Hpos x,
  rw imp_iff_not_or at H1 H2,
  split, cases H1, repeat{linarith},
  cases H2, repeat{linarith}
end

lemma nat_fin_from_real_bounded (φ : ℝ → Prop)
(Hφ : bounded {x | φ x})
: {x : ℕ | φ (↑x)}.finite :=
begin
  rw real_bounded_iff_subset_Icc at Hφ,
  rcases Hφ with ⟨M, N, Hφ⟩,
  rw [←set.finite_coe_iff],
  let S₁ := {x : ℕ | M ≤ ↑x ∧ ↑x ≤ N},
  haveI : finite S₁, begin
    let S₂ := {x : ℤ | M ≤ ↑x ∧ ↑x ≤ N},
    have : S₂.finite, begin
      have : (S₂ = S₂), from rfl,
      conv_rhs at this {simp only [S₂]},
      simp_rw [←int.le_floor, ←int.ceil_le] at this,
      rw this, clear this, clear S₁ S₂,
      apply set.finite_Icc
    end,
    haveI := set.finite_coe_iff.mpr
      (set.finite.preimage_embedding inj_posℤ this),
    apply finite.set.subset (inj_posℤ ⁻¹' S₂),
    simp only [inj_posℤ.equations._eqn_1,
      set.set_of_subset_set_of, set.preimage_set_of_eq,
      function.embedding.coe_fn_mk,
      int.cast_coe_nat, and_imp], tauto
  end,
  apply finite.set.subset S₁,
  intro x, exact @Hφ (x : ℝ)
end

lemma sum_exp {x : ℝ} (Hx : x > 0)
: summable (λ n : ℕ, real.exp (-n * x)) :=
begin
  let c := real.exp (-x),
  have : ∀n : ℕ, real.exp (-n * x) = c ^ n,
    by {intro n, rw [neg_mul, ←mul_neg, real.exp_nat_mul]},
  simp_rw this,
  apply summable_geometric_of_lt_1,
  have := real.exp_pos (-x), linarith,
  rw real.exp_lt_one_iff, linarith
end

notation (name := polynomial) R`[X]`:9000 := polynomial R

lemma quadratic_tendsto {a b c : ℝ} (Ha : a > 0)
: tendsto (λ x, eval x 
  ((C a * X ^ 2) + ((C b * X ^ 1) + (C c * X ^ 0))))
  at_top at_top :=
begin
  rw tendsto_at_top_iff_leading_coeff_nonneg,
  rw [show (0 : with_bot ℕ) = ↑(0 : ℕ), by refl, coe_lt_degree],
  let p := (C a * X ^ 2) + ((C b * X ^ 1) + (C c * X ^ 0)),
  have : p.nat_degree = 2, begin
    rw nat_degree_add_eq_left_of_nat_degree_lt,
    all_goals {rw nat_degree_C_mul_X_pow},
    linarith, swap, linarith,
    rw [show ∀(x : ℕ), x < 2 ↔ x ≤ 1, by omega],
    apply nat_degree_add_le_of_degree_le,
    apply nat_degree_C_mul_X_pow_le,
    transitivity 0, apply nat_degree_C_mul_X_pow_le,
    omega
  end,
  simp only [leading_coeff],
  rw this, split, omega,
  simp only [coeff_add, coeff_X_pow, coeff_C_mul],
  norm_num, linarith
end

lemma quadratic_lemma_1 {a b c : ℝ}
: ∀ x : ℝ,
  eval x ((C a * X ^ 2) + ((C b * X ^ 1) + (C c * X ^ 0)))
  = a * (x * x) + b * x + c :=
begin
  intro x,
  simp only [eval_C, eval_X, eval_pow, eval_mul,
    pow_one, monomial_zero_left, eval_add,
    show 2 = 1 + 1, from rfl, pow_succ, pow_zero,
    true_or, eq_self_iff_true, add_assoc, mul_one]
end

lemma quadratic_bounded {a b c : ℝ} (Ha : a > 0)
: (bounded {x : ℝ | a * (x * x) + b * x + c < 0}) :=
begin
  apply bounded_if_tends_neginf, {
    simp_rw ←quadratic_lemma_1,
    apply quadratic_tendsto, exact Ha
  }, {
    rw [←map_neg_at_top, tendsto_map'_iff],
    simp only [function.comp],
    have : ∀x : ℝ,
       (a * (-x * -x) + b * -x + c 
      = a * (x * x) + (-b) * x + c), by {intro, ring_nf},
    simp_rw [this, ←quadratic_lemma_1], clear this,
    apply quadratic_tendsto, exact Ha
  }
end

lemma summable_theta_pos (z : ℂ) (a : ℝ) (Hz : z.re > 0)
: summable (λ n : ℕ, exp (- (n + a) ^ 2 * π * z)) :=
begin
  simp only [int.cast_coe_nat, neg_mul],
  apply summable_of_norm_bounded_eventually
    (λ n : ℕ, real.exp (- n * z.re)),
  swap 3, apply_instance, swap,
  simp only [complex.norm_eq_abs], simp_rw complex.abs_exp,
  simp only [real.exp_le_exp, sq, filter.eventually_cofinite,
    not_le, neg_re, mul_re, mul_im, add_re, add_im,
    of_real_re, of_real_im,
    nat_cast_re, nat_cast_im, add_zero, mul_zero,
    zero_mul, zero_add, sub_zero, sub_lt_zero,
    lt_neg_iff_add_neg
  ],
  simp_rw [
  show ∀ x : ℝ, 
    -x * z.re + (x + a) * (x + a) * π * z.re
    = π * z.re * (x * x) + (2 * a * π - 1) * z.re * x
      + π * z.re * a * a, by {intro, ring} ],
  {
    apply nat_fin_from_real_bounded
      (λ x, π * z.re * (x * x) +
        (2 * a * π - 1) * z.re * x + π * z.re * a * a < 0),
    apply quadratic_bounded,
    have : π > 0, by exact real.pi_pos,
    nlinarith
  }, {
    apply sum_exp, exact Hz
  }
end

lemma summable_theta_neg (z : ℂ) (a : ℝ) (Hz : z.re > 0)
: summable (λ n : ℕ, exp (- (-n + a) ^ 2 * π * z)) :=
begin
  simp_rw [show
    ∀n : ℕ, (-(n : ℂ) + a) ^ 2 = (n + (-a : ℝ)) ^ 2, by
    {intro, repeat{rw sq},
      simp only [complex.of_real_neg], ring_nf}],
  exact summable_theta_pos z (-a) Hz
end

def ℂ_re_pos := {x : ℂ // x.re > 0}

@[simp] instance C_re_pos_coe :
  has_coe ℂ_re_pos ℂ := ⟨λ x, x.val⟩

lemma summable_theta (z : ℂ_re_pos) (a : ℝ)
: summable (λ n : ℤ, exp (- (-n + a) ^ 2 * π * z)) :=
begin
  apply summable_ℤ_if_summable_two_sides,
  convert summable_theta_neg z.1 a z.2,
  convert summable_theta_pos z.1 a z.2,
  ext1, congr, push_cast, ring,
end

def θ := λ (z : ℂ) (a : ℝ),
  ∑' (n : ℤ), complex.exp (- (n + a) ^ 2 * π * z)

@[reducible] def ℝexp := real.exp
def complex.sqrt (z : ℂ) := exp (log(z)/2)
notation `√` := real.sqrt
notation `√'` := complex.sqrt

open measure_theory
open measure interval_integral
open_locale topological_space

lemma integral_1 (b : ℝ) :
  ∫ x in 0 .. b, x * ℝexp (-x^2) = 1/2 * (1 - ℝexp (-b^2)) :=
begin
  set f := λ (x : ℝ), (-1/2) * ℝexp (-x^2),
  set f' := λ (x : ℝ), x * ℝexp (-x^2),
  have : deriv f = f' ∧ ∀ x : ℝ, differentiable_at ℝ f x :=
  begin
    split,
    simp_rw [deriv_const_mul_field'],
    have : ∀ x : ℝ, differentiable_at ℝ (λ x, -x^2) x,
    by {intros, simp only [differentiable_at.pow,
        differentiable_at.neg, differentiable_at_id']},
    simp_rw [λ x, deriv_exp (this x)],
    simp only [deriv.neg', deriv_pow'',
      differentiable_at_id', coe_bit0,
      algebra_map.coe_one, pow_one, deriv_id'',
      mul_one, mul_neg], ring_nf,
    intros, simp only [differentiable_at.mul,
      differentiable_at_neg_iff,
      differentiable_at_const, differentiable_at.exp,
      differentiable_at.pow, differentiable_at_id']
  end,
  rw [integral_deriv_eq_sub'
    (λ (x : ℝ), (-1/2) * ℝexp (-x^2)) this.1
    (λ x Hx, this.2 x)],
  { dsimp, ring_nf, rwa [ℝexp, real.exp_zero, mul_one] },
  { simp only [f'],
    apply continuous_on.mul, apply continuous_on_id,
    apply continuous_on.exp, apply continuous_on.neg,
    apply continuous_on.pow, apply continuous_on_id }
end

lemma integral_2 :
  ∫ x in Ioi 0, x * ℝexp (-x^2) = 1/2 :=
begin
  have : tendsto 
    (λ b, ∫ x in 0 .. b, x * ℝexp (-x^2)) at_top (𝓝 $ 1/2) :=
  begin
    simp_rw integral_1,
    rw [show 𝓝 ((1 : ℝ) / 2) = 𝓝 ((1 / 2) * 1), by rwa [mul_one]],
    apply tendsto.mul, apply tendsto_const_nhds,
    rw [show 𝓝 (1 : ℝ) = 𝓝 (1 - 0), by norm_num],
    apply tendsto.sub, apply tendsto_const_nhds,
    dsimp [ℝexp], rw real.tendsto_exp_comp_nhds_zero,
    simp_rw [show ∀ (x : ℝ),
      (-x ^ 2) = (x * x) * (-1), by {intros, nlinarith}],
    apply tendsto.at_top_mul_neg_const,
    norm_num, apply tendsto.at_top_mul_at_top,
    apply tendsto_id, apply tendsto_id
  end,
  refine tendsto_nhds_unique
    (interval_integral_tendsto_integral_Ioi
      0 _ tendsto_id) this,
  refine integrable_on_Ioi_of_interval_integral_norm_tendsto
    (1/2) 0 _ tendsto_id _,
  begin
    intro t,
    rw [integrable_on_Ioc_iff_integrable_on_Ioo,
       ←integrable_on_Icc_iff_integrable_on_Ioo],
    apply continuous_on.integrable_on_Icc,
    apply continuous_on.mul, apply continuous_on_id,
    apply continuous_on.exp, apply continuous_on.neg,
    apply continuous_on.pow, apply continuous_on_id
  end,
  dsimp [id], refine (tendsto_congr' _).mp this,
  clear this, rw eventually_eq_iff_exists_mem, use (Ioi 0),
  split, apply Ioi_mem_at_top,
  intros x Hx,
  apply integral_congr,
  intros t Ht, dsimp, rw abs_of_nonneg,
  apply mul_nonneg, have := min_le_iff.mp Ht.1,
  change 0 < x at Hx,
  cases this, repeat {linarith},
  apply le_of_lt, apply real.exp_pos
end

lemma integral_3 :
  ∫ (x : ℝ × ℝ), ℝexp (-(x.1^2+x.2^2))
= 2 * π * ∫ x in Ioi 0, x * ℝexp (-x^2) :=
begin
  rw [←integral_comp_polar_coord_symm 
    (λ (x : ℝ × ℝ), ℝexp (-(x.1^2+x.2^2)))],
  dsimp,
  simp_rw [show ∀ (x y z : ℝ),
    (z * x)^2 + (z * y)^2 = z^2 * (x^2 + y^2),
      by {intros, nlinarith},
    real.cos_sq_add_sin_sq, mul_one],
  conv_rhs {rw [mul_comm]},
  convert integral_prod_mul (λx, x * ℝexp (-x^2)) (λx, 1),
  swap 4,
  exact ((volume : measure ℝ).restrict $ Ioo (-π) π),
  { symmetry, apply measure.prod_restrict },
  { ext, rwa mul_one },
  {
    rw [measure_theory.integral_const,
        measure.restrict_apply, set.univ_inter,
        real.volume_Ioo, ennreal.to_real_of_real],
    norm_num, ring_nf,
    linarith [real.pi_pos], exact measurable_set.univ
  },
  { apply_instance }, { apply_instance }
end

lemma integral_4 :
∫ (x : ℝ × ℝ), ℝexp (-(x.1^2+x.2^2)) =
  (∫ (x : ℝ), ℝexp (-x^2))^2 :=
begin
  conv_rhs{rw sq},
  convert integral_prod_mul (λx, ℝexp (-x^2)) (λx, ℝexp (-x^2)),
  ext1, convert real.exp_add _ _, ring_nf,
  { apply_instance }, { apply_instance }
end

lemma integral_exp_neg_sq
: (∫ (x : ℝ), ℝexp (-x^2) = √π) :=
begin
  have : ∫ (x : ℝ), ℝexp (-x ^ 2) ≥ 0 :=
  begin
    apply measure_theory.integral_nonneg,
    intro a, simp only [pi.zero_apply],
    apply le_of_lt, apply real.exp_pos
  end,
  rw [←(abs_of_nonneg this), ←real.sqrt_sq_eq_abs],
  congr, rw [←integral_4, integral_3, integral_2],
  ring_nf
end

/- Functional equation for theta function -/
lemma θ_func_eqn (z : ℂ) (Hz : z.re > 0)
: θ z⁻¹ 0 = (√' z) * (θ z 0) :=
begin
  sorry
end
