---
title: «A monad is just a monoid in the category of endofunctors, what's the problem?»
date: 2018-01-29
---
<div style="display:none;">
$$\newcommand{cat}{\mathsf}%
\newcommand{id}{\mathrm{id}}%
\newcommand{bind}{\mathbin{\mathrm{\gg=}}}%
\newcommand{kleisli}{\mathbin{\mathrm{>=>}}}%
\newcommand{lkleisli}{\mathbin{\mathrm{<=<}}}%
\newcommand{natto}{\Rightarrow}%
\newcommand{Id}{\mathrm{Id}}%
$$
</div>
The quote in the title is from James Iry's
[A Brief, Incomplete, and Mostly Wrong History of Programming Languages][iry]
in which he jokingly attributes the quote to Philip Wadler, one of the
inventors of Haskell. Actually it is a slightly modified quote from
the influential category theory textbook "Categories for the working
mathematician" by Saunders Mac Lane (without the part about problems.)
It is passed around in functional programming circles, but nobody ever
seems to try to explain what it means in detail. Is it just a joke?
Trying to make your head explode? Let's try to understand what it
means.

For a serious attempt at understanding this quote, you should already
kind of know what the individual words mean. You've seen the `Monad`
and `Monoid` type classes in Haskell, you should also have had some
exposure to the basics of category theory, in particular functors,
natural transformations, and products. You should also know the basics
of set theory.

Nothing in this is new, you can find it in most category theory
textbooks; [Bartosz Milewski][milewski] has a
[section about the categorical meaning of monads][bartosz-section]. There
was even a similarly-titled [blog article by Axel Wagner][wagner]
recently (published while I was writing this), which also explains
categories and functors, but leaves out the stuff about monoidal
categories. You're invited to check out these other sources if you get
stuck reading this article. If nothing else, this article is just an
account of something I learned recently.

The title should more precisely be: "A monad (in a category $C$) is a
monoid object in the monoidal category of endofunctors (of $C$), where
the tensor product is given by composition." We're going to disect
this definition and see how the parts fit together.

[iry]: http://james-iry.blogspot.de/2009/05/brief-incomplete-and-mostly-wrong.html
[milewski]: https://bartoszmilewski.com/
[bartosz-section]: https://bartoszmilewski.com/2016/12/27/monads-categorically/
[wagner]: https://blog.merovius.de/2018/01/08/monads-are-just-monoids.html


# What is a monoid?

Recall that a *monoid* is a set $M$ equipped with two additional data:
First, a binary operation $\mu : M\times M \to M$, often called
multiplication. The multiplication is often written using some infix
operator symbol, e.g. $a\diamond b$ instead of $\mu(a,b)$. It is
required to satisfy an *associative law*, i.e., $a\diamond(b\diamond c)
= (a\diamond b)\diamond c$ should hold for all $a, b, c\in M$. The
second datum is a particular element $e\in M$ which acts as a left and
right *identity element*, i.e. for all $a\in M$ we have $e\diamond a =
a = a\diamond e$.

Of course you know this already. Haskell has a `Monoid` typeclass
which provides a value `mempty :: m`, which represents the identity
element $e$, and a function `mappend :: m -> m -> m` which represents
the binary operation $\mu$ (in curried form.) Haskell has no way of
enforcing the laws, but it is a matter of convention to define a
`Monoid` instance only if the laws hold.

Now let us step back and, in the spirit of category theory, try to
reformulate this definition in terms of objects and arrows, or in
*point-free* form. We need a set $M$, i.e. an object in the category
$\cat{Set}$. Our binary operation is just a morphism $\mu : M\times M
\to M$ in this categeory. What about the identity element? At this
point we have to fix an arbitrary singleton set $I = \{*\}$. It
doesn't matter which, since all singleton sets are isomorphic, but it
is customary to denote this element by an asterisk. (In Haskell we
have the unit type `()` as a canonical one-element type.) Let $\eta :
I\to M$ be the function $\eta(*) = e$. (Notice that for each set $A$,
specifying a morphism $I\to A$ is equivalent to specifying an element
of $A$.)

The associative law is $\mu(a,\mu(b,c)) = \mu(\mu(a,b), c)$, or
$\mu((\id_M\times\mu) (a, (b, c))) = \mu((\mu\times\id_M)((a, b), c))$
for all $a, b, c\in M$. Note the difference in "shape" between
$(a,(b,c))$ and $((a,b),c)$. To write this equation in point-free
form, we have to introduce a function that can translate between those
shapes:

$$\alpha : M\times(M\times M) \to (M\times M)\times M\\
\alpha(a, (b, c)) = ((a, b), c)$$

This function is obviously an isomorphism, it is called an
*associator*. We can now give the associative law in the form of a
*commutative diagram*:

$$\require{AMScd}
\begin{CD}
M\times(M\times M) @>{\id_M\times\mu}>> M\times M @>\mu>> M  \\
@V{\alpha}VV                                @.              @| \\
(M\times M)\times M @>{\mu\times\id_M}>> M\times M @>\mu>> M
\end{CD}
$$

Calling the diagram *commutative* means that all paths between two
given vertices denote the same morphism. So here that means
$\mu\circ(\mu\times \id_M)\circ\alpha = \mu\circ(\id_M\times\mu)$, or,
with elements: $\mu(\mu(a,b), c) = \mu(a,\mu(b,c))$. Just our
associativity law.

To bring the left identity law, $\mu(e, a) = a$, into point-free form,
we have to replace $e$ by $\eta(*)$, so the left side becomes
$\mu(\eta(*), a) = (\mu \circ (\eta, \id_M))(*,a)$. We obtain the
following commutative diagram, with the right identity law already included:

$$\begin{CD}
I\times M @>{\eta\times\id_M}>> M\times M @<{\id_M\times\eta}<< M\times I \\
@|                               @V{\mu}VV                      @|        \\
I\times M @>{\lambda}>>              M    @<{\rho}<<         M\times I
\end{CD}$$

where $\lambda : I\times M\to M, \lambda(*,a) = a$ and $\rho : M\times
I\to M, \rho(a,*) = a$ are isomorphisms that perform a role that is
similar to the associator $\alpha$. They are called *left* and *right unitor*.

Now that we have brought the definition into an abstract categorical
form, we may start to think about similar constructions in other
categories.

# What is a monoidal category?

A monoid gives us a way to multiply elements of a *set*. Can we also
somehow multiply objects of a category? After all, a set can be
thought of as a *discrete category*, that is, a category where the
only morphisms are identites.

To define a monoidal category, start with a category $C$. For the
multiplication, we're going to need a functor $\otimes : C\times C\to
C$, called the *tensor product*. The identity is going to be some
object $I\in C$, the *unit object*. Ideally, we would like to have
some analog of the monoid laws as before, that is, $A\otimes(B\otimes
C) = (A\otimes B)\otimes C$, $I\otimes A=A$ and $A\otimes I =
A$. However, this is not going to hold in most interesting
cases. Remember the discussion about the associator which translates
between different tuple shapes above? Similarly, for a general
monoidal category we're going to need natural translator isomorphisms

$$\alpha_{ABC} : A\otimes (B\otimes C) \to (A\otimes B)\otimes C,$$
$$\lambda_A : I\otimes A \to A,$$
$$\rho_A : A\otimes I\to A.$$

Sometimes equality does hold, however, and a monoidal category where
this is the case, or in which these translation morphisms are
identities, is called *strict*.

We demand that they satisfy the following *coherence laws* to make
sense, expressed as commutative diagrams.

$$\begin{CD}
A\otimes(I\otimes B) @>{\alpha_{AIB}}>> (A\otimes I)\otimes B  \\
@V{\id_A\otimes\lambda_B}VV         @V{\rho_A\otimes\id_B}VV \\
A\otimes B           @=           A\otimes B
\end{CD}$$

and the so-called pentagon

$$\begin{CD}
A\otimes(B\otimes(C\otimes D)) @= A\otimes(B\otimes(C\otimes D)) \\
@V{\alpha}VV                           @V{\id_A\otimes\alpha}VV      \\
(A\otimes B)\otimes(C\otimes D) @.  A\otimes((B\otimes C)\otimes D)\\
@V{\alpha}VV                           @V{\alpha}VV              \\
((A\otimes B)\otimes C)\otimes D @<{\alpha\otimes \id_D}<< (A\otimes (B\otimes C))\otimes D 
\end{CD}$$

Unfortunately, for technical reasons, my diagram doesn't quite have a
pentagonal shape. I also hope that the simplified notation doesn't
cause confusion. The upper left $\alpha$ stands for
$\alpha_{A,B,C\otimes D}$, for example. It should always be clear from
the context what is meant.

*Examples:*

1) We have already seen an example of a monoidal category, namely
 $\cat{Set}$ with the ordinary product for the tensor product and a
 singleton $I = \{*\}$ for the unit object, with

$$\alpha((a, b), c) = (a, (b, c))$$
$$\lambda(*,a) = a$$
$$\rho(a,*) = a$$.

2) A similar example is the category $\cat{Set}$ again, only this time
we take the coproduct (disjoint union, `Either`) for the tensor
product, and the empty set $\emptyset$ for the unit object. The
associator and unitors can be defined in the obvious way.

3) In linear algebra, we work in the category $\cat{Vect}_K$ of
vector spaces over a field $K$, where the morphisms are $K$-linear
maps. It is a monoidal category with respect to the usual tensor
product of vector spaces, with $K$ considered as a vector space over
itself as the unit object. Similarly, for a commutative ring $R$, the
category of $R$-modules is a monoidal category wrt. the tensor product
over $R$.

# What is a monoid object?

A monoid object is at this point a straight-forward generalization of a
monoid to monoidal categories. Consider a fixed monoidal category $(C,
\otimes, I, \alpha, \lambda, \rho)$. A monoid object in this category
is an object $M\in C$ together with morphisms

$$\mu : M\otimes M\to M$$
and
$$\eta : I\to M$$

such that the following diagrams commute:

$$\begin{CD}
M\otimes(M\otimes M) @>{\id_M\otimes\mu}>> M\otimes M @>\mu>> M   \\
@V{\alpha_{MMM}}VV                           @.               @|  \\
(M\otimes M)\otimes M @>{\mu \otimes \id_M}>> M\otimes M @>\mu>> M
\end{CD}
$$

and 
$$\begin{CD}
I\otimes M @>{\eta\otimes\id_M}>> M\otimes M @<{\id_M\otimes\eta}<< M\otimes I\\
@|                                  @V{\mu}VV                        @|     \\
I\otimes M @>{\lambda_M}>>               M          @<{\rho_M}<<          M\otimes I
\end{CD}
$$

You can easily convince yourself that a monoid is just a monoid object
in $(\cat{Set}, \times)$.

Exercises: What is a monoid object in $(\cat{Set},\sqcup)$? If you're
familiar with tensor products of abelian groups, try to figure out
what a monoid object in $(\cat{Ab}, \otimes)$ is.

# What is the category of endofunctors?

Let $C$ be a category. An endofunctor of $C$ is a functor $C\to
C$. Morphisms of functors are natural transformations. If $F,G,H$ are
endofunctors of $C$, and $\alpha:F\natto G$, $\beta : G\natto H$ are natural
transformations, we can define the composition component-wise,

$$ (\beta\circ\alpha)_X = \alpha_X\circ\beta_X. $$

It is easy to check that this *vertical composition* results in a
natural transformation $\beta\circ\alpha : F\natto H$, and that it is
associative and acts as expected on identities, so we have a category
$\mathcal{E}$ of endofunctors of $C$. To arrive at monads eventually,
we take the *composition* of functors as our tensor product and the
identity functor as unit object.

This choice has the nice property that this will actually be a strict
monoidal category, because $F\circ (G\circ H) = (F\circ G)\circ H$,
$\Id\circ F = F = F\circ\Id$. However, the action of the composition
functor $\circ: \mathcal{E}\times\mathcal{E}\to\mathcal{E}$, our
tensor product, on morphisms is a little tricky.

Let $f: F\to F'$, $g:G\to G'$ be two morphisms in $\mathcal{E}$. We want to
construct a morphism $f\otimes g: F\circ G\to F'\circ G'$. Let's
examine the issue for a given object $A$ of $C$. Starting at
$F(G(A))$, we can apply the $G(A)$-component of $f$,

$$f_{G(A)} : F(G(A))\to F'(G(A)),$$

then lift the $A$-component of $g$ over $F'$ to obtain a morphism

$$F'(g_A) : F'(G(A)) \to F'(G'(A)).$$

We could, however, also apply $F(g_A)$ first and then $f_{G'(A)}$. It
turns out that this choice does not matter, or in other words, the
following diagram is commutative for all objects $A$ of $C$:

$$\begin{CD}
FG(A) @>{f_{G(A)}}>> F'G(A) \\
@V{F(g_A)}VV        @V{F'(g_A)}VV \\
FG'(A) @>{f_{G'(A)}}>> F'G'(A)
\end{CD}
$$

and we obtain the desired natural transformation $f\otimes g$. It is
called the *horizontal composition* of $f$ and $g$ and usually denoted
$f\bullet g$. Note that by convention, sometimes an object stands for
the identity morphism belonging to that object. So if you see
something like $f\bullet G$, this is the same as $f\bullet \id_G$
etc., and you could work out what it means by applying the
definition. There's a useful shortcut however, just remember that
$f\bullet G$ is the natural transformation whose components are
$f_{G(A)}$, while $F\bullet g$ has the components $F(g_A)$, for all
$A$.

# Putting it together: What is a monad?

See title of this post (j/k). It is probably worthwile to walk through
the whole construction again. Let $M\in\mathcal{E}$ be a monoid object
in the category $\mathcal{E}$ of endofunctors of $C$, where the tensor
product is given by composition of functors. That is, $M$ is a functor
$C\to C$, and there are two natural transformations

$$\mu : M\circ M \natto M,$$
the multiplication, and
$$\eta : \Id\natto M,$$
the unit.

In Haskell, the multiplication is called `join` with the signature
`join :: m (m a) -> m a`; the unit is called `return` (or `pure`) with
the signature `return :: a -> m a`.

We require associativity:

$$\begin{CD}
M\circ M\circ M @>{\id_M\bullet\mu}>> M\circ M @>{\mu}>> M \\
@|                                      @.               @| \\
M\circ M\circ M @>{\mu\bullet\id_M}>>  M\circ M @>{\mu}>> M
\end{CD}$$

and $\eta$ should be a left and right identity

$$\begin{CD}
\Id \circ M @>{\eta\bullet\id_M}>> M\circ M @<{\id_M\bullet\eta}<< M\circ \Id \\
@|                                         @V{\mu}VV                    @| \\
M  @=                                      M                  @=        M
\end{CD}$$

The corresponding equations are

$$\begin{align*}
\mu \circ (\mu\bullet\id_M) &= \mu \circ (\id_M\bullet\mu) \\
\mu\circ(\eta\bullet\id_M) &= \id_M \\
\mu\circ(\id_M\bullet\eta) &= \id_M
\end{align*}$$

or, in Haskell:

`join . join == join . fmap join`,

`join . return == id`,

`join . fmap return == id`.

Or, in plain english: In a nested monad structure, it doesn't matter
in which order the layers are `join`ed (associativity). When
`return`ing a monadic value and then `join`ing, it doesn't matter
whether the `return` wraps the given monadic value or whether the
`return` is lifted inside, in both cases we end up where we started
(left and right identity.)

# Monad laws

In Haskell, the `Monad` typeclass is defined in terms of two functions, `return` and `>>=` (called "bind"), and instances are supposed to satisfy the following "Monad laws":

1. `m >>= return == m`
2. `return x >>= f == f x`
3. `(m >>= f) >>= g == m >>= (\x -> f x >>= g)`

There's also a `join` function, which can be defined in terms of bind, and vice versa:

	m >>= f = join (fmap f m)

	join mma = mma >>= id

Thus we have another notion of "monad", and we can translate back and
forth between the categorical and the Haskell view. We're going to
show that the two notions are equivalent.

Until now the discussion has been
agnostic about the nature of our base category $C$, but now we need a
concrete category, where objects have elements and morphisms are
functions. So in the following, let's say $C=\cat{Set}$, or
$C=\cat{Hask}$, whichever you prefer.

## Theorem:

An endofunctor $M\in\mathcal E$ is a monad (in the
categorical sense) if and only if it satisfies the following
conditions, which are known as “Monad Laws”:

1. $m\bind \eta = m$ for $m\in M(A)$
2. $\eta(x) \bind f = f(x)$ for $x\in A$ and $f: A\to M(B)$
3. $(m\bind f)\bind g = m \bind (\lambda x . f(x) \bind g)$ for $m\in M(A)$, $f:A\to M(B)$ and $g:B\to M(C)$.

### Proof:

First we're going to show that a monad $M\in\mathcal E$ satisfies the
monad laws.

Recall that $\bind$ is defined by $m\bind f = \mu(M(f)(m))$ for $m\in M(A)$, $f:A\to M(B)$, and conversely $\mu$ is defined by $\mu(x) = x\bind\id$ for $x\in M(M(A))$. Use of these definitions will not be specially marked in the following.

1. Let $m\in M(A)$. Then $m\bind\eta = \mu(M(\eta)(m)) \stackrel*= m$,
where the marked equality holds by the *right identity law*, $\mu\circ
(M\bullet\eta) = \id$.

2. Let $x\in A$ and $f: A\to M(B)$. Then

$$\eta(a)\bind f = \mu(M(f)(\eta(x))) \stackrel*= \mu(\eta(f(x)))
\stackrel{**}= f(x)$$

where the first equality marked $*$ holds because $\eta$ is a natural
transformation $\Id\to M$, hence $M(f)\circ \eta_A =
\eta_{F(A)}\circ f$, and the one marked $**$ holds by the *left
identity law*, $\mu\circ (\eta\bullet M) = \id$.

3. Let $m\in M(A)$, $f:A\to M(B)$, $g:B\to M(C)$.

$$\begin{align*}
(m\bind f)\bind g &= \mu(M(f)(m)) \bind g \\
&= \mu(M(g)(\mu(M(f)(m)))) \\
&\stackrel*= \mu(\mu(M(M(g)\circ f)(m))) \\
&\stackrel{**}=\mu(M(\mu)(M(M(g)\circ f)(m))) \\
&= \mu(M(\mu\circ M(g) \circ f)(m)) \\
&= m \bind \mu\circ M(g) \circ f \\
&= m \bind (\lambda x . f(x) \bind g)
\end{align*}
$$

where the $*$ holds because of naturality of $\mu: M\circ M\to M$:
$M(g)\circ \mu_B = \mu_{MC}\circ M(M(g))$, and $**$ holds by the
*associative law*, $\mu\circ(\mu\bullet M) =
\mu\circ(M\bullet\mu)$. 

Conversely, let $M\in\mathcal E$ be an endofunctor that satisfies the
monad laws 1, 2 and 3.

1. Let $m\in M(A)$. Then by law 1, $\mu(M(\eta)(m)) = m\bind \eta \stackrel*=
m$, so the *right identity law* $\mu\circ(M\bullet\eta)=\id$ follows.

2. Let $m\in M(A)$. Then by law 2, $\mu(\eta(m)) = \eta(m)\bind\id
\stackrel*= \id(m) = m$. This shows the *left identity law*,
$\mu\circ(\eta\bullet M) = \id$.

3. Let $m\in MMM(A)$. Then
$$\begin{align*}
\mu(M(\mu)(m)) &= m\bind\mu \\
&= m\bind(\lambda x.x\bind\id) \\
&\stackrel*= (m\bind\id)\bind\id \\
&= \mu(\mu(m))
\end{align*}$$

where we used law 3. This shows the *associative law*, $\mu\circ(M\bullet\mu) = \mu\circ(\mu\bullet M)$.

# Notes

* I have completely ignored the issue of naturality of `return`, `>>=`
  and `join`. According to the definition, these functions should be
  natural transformations. We don't have to worry, however, because
  due to parametric polymorphism it is indeed impossible to write a
  function `h :: F a -> G a` between functors `F` and `G` that is not
  a natural transformation. There is a whole class of such theorems,
  which go under the slogan "Theorems for free", among them: the only
  (total) function `a -> a` is the identity, and if a type of kind `*
  -> *` can be a `Functor` at all, it has a unique instance. I plan to
  write an article about this topic later.

* The monad laws can be more elegantly put in terms of _Kleisli
  composition_, which is simultaneously easily understood as the
  composition in a special category and easily defined in terms of
  "bind". This results in an interpretation of "bind" as some kind of
  "Kleisli application", so our intuitions about normal function
  application and composition directly carry over. But this topic
  deserves its own article.