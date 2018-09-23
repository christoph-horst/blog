---
title: These are not the monoids you're looking for...
date: 2018-09-18
---

When people first encounter the meme that monads are just monoids (in
the category of endofunctors), some get the entirely wrong idea. Recall the
monad laws:

* `m >>= pure == m`
* `pure a >>= f == f a`
* `(m >>= f) >>= g == m >>= (\a -> f a >>= g)`

If you squint a little, doesn't this look a bit like a right and left
identity law and an associativity law? Just like the monoid laws?
Let's squint a little harder and rewrite the laws in terms of *Kleisli
composition*, that is, the following operator:

``` haskell
(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(f >=> g) a = f a >>= g
```

The laws then become

* `f >=> pure == f`
* `pure >=> g == g`
* `(f >=> g) >=> h == f >=> (g >=> h)`

Very familiar. So, isn't this the monoid we're looking for? With
`pure` being the identity and `>=>` the append operation?

**NO!**

These aren't the laws of a monoid, but the laws of a category, the
*Kleisli category* corresponding to the monad. A category is somewhat
similar to a monoid -- in fact, a monoid can be interpreted as a
special case of a category. The difference is: In a monoid, any two
elements can be appended, `x <> y` is always defined. In contrast, in
a category, the composition of arrows[^elements] is defined only if
the endpoint of the one arrow coincides with the starting point of the
next, so the composition is a *partial operation*.  You can see this
from the type of `(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a
-> m c)`. The composition `f >=> g` does not typecheck if the `b` in
the return type of `f` is different from the `b` in the argument type
of `g`.

[^elements]: A category consists of objects and arrows, an arrow
starts at one object and ends at another (or loop back to the same
object). The term "element" is not used for these.

You can read a full account about how a monad is a monoid in my
article [«A monad is just a monoid in the category of endofunctors,
what's the problem?»](/posts/whats-the-problem.html).

The TL;DR is: The identity is `pure`, that much is correct, but the
append operation is a function that is called `join :: Monad m => m (m
a) -> m a` in Haskell. This seems incomprehensible at first, that's
because a monad is not in any way a monoid in the usual sense, but an
arrow-theoretic generalization of a monoid, a thing called a *monoid
object*, that can be defined in *monoidal categories*. If you want to
know how this makes sense, seriously, read my article.